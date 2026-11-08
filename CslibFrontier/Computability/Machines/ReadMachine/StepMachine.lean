/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.ReadMachine.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.StepMachine.Basic

/-!
# Step machines simulating read machines

A read machine reads its input at an address; a `Turing.StepMachine` sees the cell under its head
and moves it by one cell per step. `Turing.ReadMachine.toStepMachine` keeps the position of the head
in its state: before each step of the read machine that reads the address `a`, it moves the head to
the cell of `a`, at position `a + 1`, and then takes that step on the bit there. It stops at the
blank after the input if `a` is beyond it, which reads as `false`, as for the read machine.

## Main definitions

* `Turing.ReadMachine.toStepMachine`: the simulating step machine.

## Main results

* `Turing.ReadMachine.computes_toStepMachine`: if the read machine halts with an output, the step
  machine computes that output.
-/

@[expose] public section

namespace Turing

namespace ReadMachine

variable {σ : Type*} (m : ReadMachine σ)

/-- The step of the read machine, keeping the head position `pos`. -/
def stepAt (q : σ) (pos : ℕ) (b : Bool) : (σ × ℕ) × SignType × List Bool :=
  ((((m.step q b).1, pos)), 0, (m.step q b).2)

/-- The step machine simulating `m`, with the position of its head in its state. -/
def toStepMachine : StepMachine (σ × ℕ) Bool Bool where
  init := (m.init, 1)
  halt q := m.halt q.1
  step q a :=
    match m.addr q.1 with
    | none => m.stepAt q.1 q.2 false
    | some A =>
      if q.2 = A + 1 then m.stepAt q.1 q.2 (a.getD false)
      else if q.2 < A + 1 then
        if a = none ∧ q.2 ≠ 0 then m.stepAt q.1 q.2 false
        else ((q.1, q.2 + 1), 1, [])
      else ((q.1, q.2 - 1), -1, [])

variable {m} {x : List Bool}

/-- The configurations of the step machine that represent `c`: the state of `c` with the head at
the position in the state, and the same output. -/
def Represents (c : Cfg σ) (d : StepMachine.Cfg (σ × ℕ) Bool x) : Prop :=
  d.state.1 = c.state ∧ d.state.2 = d.pos.val ∧ d.out = c.out

/-- The step of the read machine itself. -/
theorem stepCfg_read {d : StepMachine.Cfg (σ × ℕ) Bool x} (hhalt : m.halt d.state.1 = false)
    {b : Bool} (hb : (m.toStepMachine).step d.state (MultiTapeTM.inputSymbolAt x d.pos) =
      m.stepAt d.state.1 d.state.2 b) :
    m.toStepMachine.stepCfg d =
      ⟨((m.step d.state.1 b).1, d.state.2), d.pos, d.out ++ (m.step d.state.1 b).2⟩ := by
  have h : (m.toStepMachine).halt d.state = false := hhalt
  simp only [StepMachine.stepCfg, StepMachine.stepAt, h, Bool.false_eq_true, ↓reduceIte, hb,
    stepAt, moveInputPos_zero]

theorem readBit_eq {q : σ} {A : ℕ} (h : m.addr q = some A) : m.readBit x q = x.getD A false := by
  simp [readBit, h]

/-- The walk of the head to the cell of the address read next, and the step there. -/
theorem exists_iterate_stepCfg_some {q : σ} {A : ℕ} (hA : m.addr q = some A)
    (hhalt : m.halt q = false) (out : List Bool) :
    ∀ w (d : StepMachine.Cfg (σ × ℕ) Bool x), d.state = (q, d.pos.val) → d.out = out →
      (d.pos.val - (A + 1)) + ((A + 1) - d.pos.val) ≤ w →
      ∃ k, Represents (m.next x ⟨q, out⟩) ((m.toStepMachine).stepCfg^[k] d) := by
  intro w
  induction w with
  | zero =>
    intro d hs ho hw
    have hpos : d.pos.val = A + 1 := by omega
    have hb : (m.toStepMachine).step d.state (MultiTapeTM.inputSymbolAt x d.pos) =
        m.stepAt d.state.1 d.state.2 (x.getD A false) := by
      simp [toStepMachine, hs, hA, hpos, MultiTapeTM.inputSymbolAt, List.getD_eq_getElem?_getD]
    refine ⟨1, ?_⟩
    rw [Function.iterate_one, stepCfg_read (by simp [hs, hhalt]) hb]
    simp [Represents, next, hhalt, readBit_eq hA, hs, ho]
  | succ w ih =>
    intro d hs ho hw
    by_cases hpos : d.pos.val = A + 1
    · exact ih d hs ho (by omega)
    by_cases hlt : d.pos.val < A + 1
    · by_cases hend : MultiTapeTM.inputSymbolAt x d.pos = none ∧ d.pos.val ≠ 0
      · -- the head is on the blank after the input: the address is beyond it
        have hgt : x.length ≤ A := by
          obtain ⟨h₁, h₂⟩ := hend
          simp only [MultiTapeTM.inputSymbolAt, h₂, ↓reduceIte, List.getElem?_eq_none_iff] at h₁
          omega
        have hb : (m.toStepMachine).step d.state (MultiTapeTM.inputSymbolAt x d.pos) =
            m.stepAt d.state.1 d.state.2 false := by
          simp only [toStepMachine, hs, hA]
          simp [hpos, hlt, hend]
        refine ⟨1, ?_⟩
        rw [Function.iterate_one, stepCfg_read (by simp [hs, hhalt]) hb]
        simp [Represents, next, hhalt, readBit_eq hA, hs, ho, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none hgt]
      · -- move right
        have hmove : (moveInputPos d.pos 1).val = d.pos.val + 1 := by
          rw [MultiTapeTM.val_moveInputPos_pos]
          have : d.pos.val ≤ x.length := by
            by_contra hc
            apply hend
            refine ⟨?_, by omega⟩
            simp only [MultiTapeTM.inputSymbolAt, show d.pos.val ≠ 0 by omega, ↓reduceIte,
              List.getElem?_eq_none_iff]
            omega
          omega
        have hstep : (m.toStepMachine).stepCfg d =
            ⟨(q, d.pos.val + 1), moveInputPos d.pos 1, out⟩ := by
          have hend' : ¬(MultiTapeTM.inputSymbolAt x d.pos = none ∧ ¬d.pos = 0) :=
            fun h => hend ⟨h.1, fun h0 => h.2 (Fin.ext h0)⟩
          simp only [StepMachine.stepCfg, StepMachine.stepAt, toStepMachine, hs, hhalt, hA]
          simp [hpos, hlt, hend', ho]
        obtain ⟨k, hk⟩ := ih ⟨(q, d.pos.val + 1), moveInputPos d.pos 1, out⟩
          (by simp [hmove]) rfl (by simp only [hmove]; omega)
        exact ⟨k + 1, by rw [Function.iterate_succ_apply, hstep]; exact hk⟩
    · -- move left
      have hmove : (moveInputPos d.pos (-1)).val = d.pos.val - 1 :=
        MultiTapeTM.val_moveInputPos_neg _
      have hstep : (m.toStepMachine).stepCfg d =
          ⟨(q, d.pos.val - 1), moveInputPos d.pos (-1), out⟩ := by
        simp only [StepMachine.stepCfg, StepMachine.stepAt, toStepMachine, hs, hhalt, hA]
        simp [hpos, hlt, ho]
      obtain ⟨k, hk⟩ := ih ⟨(q, d.pos.val - 1), moveInputPos d.pos (-1), out⟩
        (by simp [hmove]) rfl (by simp only [hmove]; omega)
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, hstep]; exact hk⟩

/-- **One step of the read machine** is simulated by steps of the step machine; a halted read
machine stays put, in zero steps. -/
theorem exists_iterate_stepCfg {c : Cfg σ} {d : StepMachine.Cfg (σ × ℕ) Bool x}
    (h : Represents c d) : ∃ k, Represents (m.next x c) ((m.toStepMachine).stepCfg^[k] d) := by
  cases hhalt : m.halt c.state
  · obtain ⟨c, out⟩ := c
    obtain ⟨hq, hp, ho⟩ := h
    have hs : d.state = (c, d.pos.val) := Prod.ext hq hp
    simp only at hhalt ho
    rcases hA : m.addr c with _ | A
    · have hb : (m.toStepMachine).step d.state (MultiTapeTM.inputSymbolAt x d.pos) =
          m.stepAt d.state.1 d.state.2 false := by
        simp [toStepMachine, hs, hA]
      refine ⟨1, ?_⟩
      rw [Function.iterate_one, stepCfg_read (by simp [hs, hhalt]) hb]
      simp [Represents, next, hhalt, readBit, hA, hs, ho]
    · exact exists_iterate_stepCfg_some hA hhalt out _ d hs ho le_rfl
  · exact ⟨0, by simpa [next, hhalt] using h⟩

/-- The steps of the read machine are simulated by the step machine. -/
theorem exists_run_represents (x : List Bool) (n : ℕ) :
    ∃ t, Represents (m.run x n) ((m.toStepMachine).run x t) := by
  induction n with
  | zero => exact ⟨0, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨k, hk⟩ := exists_iterate_stepCfg ht
    refine ⟨k + t, ?_⟩
    rw [run_add, runFrom_one, StepMachine.run, Function.iterate_add_apply]
    exact hk

/-- **The step machine computes the output of the read machine**, if it halts. -/
theorem computes_toStepMachine {x : List Bool} {n : ℕ} (h : m.halt (m.run x n).state = true) :
    (m.toStepMachine).Computes x (m.run x n).out := by
  obtain ⟨t, hq, -, ho⟩ := exists_run_represents (m := m) x n
  have hhalt : (m.toStepMachine).halt ((m.toStepMachine).run x t).state := by
    change m.halt ((m.toStepMachine).run x t).state.1 = true
    rw [hq]
    exact h
  obtain ⟨t', -, ht', hrun⟩ := StepMachine.exists_haltsAt_le _ hhalt
  exact ⟨t', ht', by rw [hrun, ho]⟩

/-- The configurations of the step machine on `x` that follow the read machine: the head at the
position in the state, and the state and the output of a configuration of the read machine. -/
def Follows (x : List Bool) (d : StepMachine.Cfg (σ × ℕ) Bool x) : Prop :=
  d.state.2 = d.pos.val ∧ ∃ j, d.state.1 = (m.run x j).state ∧ d.out = (m.run x j).out

/-- A step of the step machine keeps it following the read machine. -/
theorem Follows.stepCfg {d : StepMachine.Cfg (σ × ℕ) Bool x} (h : Follows (m := m) x d) :
    Follows (m := m) x ((m.toStepMachine).stepCfg d) := by
  obtain ⟨hp, j, hq, ho⟩ := h
  have hs : d.state = ((m.run x j).state, d.pos.val) := Prod.ext hq hp
  by_cases hhalt : m.halt (m.run x j).state
  · have : (m.toStepMachine).stepCfg d = d := by
      simp [StepMachine.stepCfg, toStepMachine, hs, hhalt]
    rw [this]; exact ⟨hp, j, hq, ho⟩
  -- a step of the read machine, on its bit
  have hread {b : Bool} (hb : (m.toStepMachine).step d.state (MultiTapeTM.inputSymbolAt x d.pos) =
      m.stepAt d.state.1 d.state.2 b) (hbit : b = m.readBit x (m.run x j).state) :
      Follows (m := m) x ((m.toStepMachine).stepCfg d) := by
    rw [stepCfg_read (by simp [hs, hhalt]) hb]
    refine ⟨by simp [hs], j + 1, ?_, ?_⟩
    · simp [hs, run_add, runFrom_one, next, hhalt, hbit]
    · simp [hs, run_add, runFrom_one, next, hhalt, hbit, ho]
  rcases hA : m.addr (m.run x j).state with _ | A
  · exact hread (b := false) (by simp [toStepMachine, hs, hA]) (by simp [readBit, hA])
  · by_cases h₁ : d.pos.val = A + 1
    · exact hread (b := x.getD A false)
        (by simp [toStepMachine, hs, hA, h₁, MultiTapeTM.inputSymbolAt, List.getD_eq_getElem?_getD])
        (by simp [readBit, hA, List.getD_eq_getElem?_getD])
    by_cases h₂ : d.pos.val < A + 1
    · by_cases h₃ : MultiTapeTM.inputSymbolAt x d.pos = none ∧ d.pos.val ≠ 0
      · have hgt : x.length ≤ A := by
          obtain ⟨h₄, h₅⟩ := h₃
          simp only [MultiTapeTM.inputSymbolAt, h₅, ↓reduceIte, List.getElem?_eq_none_iff] at h₄
          omega
        exact hread (b := false) (by simp only [toStepMachine, hs, hA]; simp [h₁, h₂, h₃])
          (by simp [readBit, hA, List.getD_eq_getElem?_getD, List.getElem?_eq_none hgt])
      · have h₃' : ¬(MultiTapeTM.inputSymbolAt x d.pos = none ∧ ¬d.pos = 0) :=
          fun h => h₃ ⟨h.1, fun h0 => h.2 (Fin.ext h0)⟩
        have hmove : (moveInputPos d.pos 1).val = d.pos.val + 1 := by
          rw [MultiTapeTM.val_moveInputPos_pos]
          have : d.pos.val ≤ x.length := by
            by_contra hc
            apply h₃
            refine ⟨?_, by omega⟩
            simp only [MultiTapeTM.inputSymbolAt, show d.pos.val ≠ 0 by omega, ↓reduceIte,
              List.getElem?_eq_none_iff]
            omega
          omega
        refine ⟨?_, j, ?_, ?_⟩ <;>
          simp only [StepMachine.stepCfg, StepMachine.stepAt, toStepMachine, hs, hhalt, hA] <;>
          simp [h₁, h₂, h₃', hmove, ho]
    · have hmove : (moveInputPos d.pos (-1)).val = d.pos.val - 1 :=
        MultiTapeTM.val_moveInputPos_neg _
      refine ⟨?_, j, ?_, ?_⟩ <;>
        simp only [StepMachine.stepCfg, StepMachine.stepAt, toStepMachine, hs, hhalt, hA] <;>
        simp [h₁, h₂, hmove, ho]

/-- **The states of the step machine**: every state it reaches is a state of the read machine,
with a position at most the length of the input plus one. -/
theorem exists_state_run (x : List Bool) (t : ℕ) :
    ∃ j, ((m.toStepMachine).run x t).state = ((m.run x j).state,
      ((m.toStepMachine).run x t).state.2) ∧ ((m.toStepMachine).run x t).state.2 ≤ x.length + 1 :=
  by
  have h : Follows (m := m) x ((m.toStepMachine).run x t) := by
    induction t with
    | zero => exact ⟨rfl, 0, rfl, rfl⟩
    | succ t ih => rw [StepMachine.run_succ]; exact ih.stepCfg
  obtain ⟨hp, j, hq, -⟩ := h
  refine ⟨j, Prod.ext hq rfl, ?_⟩
  rw [hp]
  exact Nat.lt_succ_iff.mp ((m.toStepMachine).run x t).pos.isLt

end ReadMachine

end Turing
