/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Function.Iterate

/-!
# Machines reading their input by address

A read machine has a state, and in each state either halts or takes a step. A step may read the
bit of the input at an address given by the state, and may emit output bits. It is a convenient
intermediate model for space-bounded algorithms that consult their input at computed positions:
`Turing.StepMachine`s, which move a head one cell at a time, simulate read machines by keeping
the head position in their state.

## Main definitions

* `Turing.ReadMachine`: read machines, with an initial state, a halting test, the address read by
  a step and the step itself.
* `Turing.ReadMachine.run`: the configuration after a number of steps.

## Main results

* `Turing.ReadMachine.run_add`: runs compose.
* `Turing.ReadMachine.runFrom_loop`: a loop of a read machine, emitting a word in each round.
-/

@[expose] public section

namespace Turing

/-- A machine reading its input by address. In a state `q` that is not halting, it reads the input
bit at `addr q` (if any; `false` beyond the input or without an address), and moves to
`(step q b).1`, emitting `(step q b).2`. -/
structure ReadMachine (σ : Type*) where
  /-- The initial state. -/
  init : σ
  /-- The halting states. -/
  halt : σ → Bool
  /-- The address of the input bit read by the next step, if any. -/
  addr : σ → Option ℕ
  /-- The next state and the emitted bits, given the bit read. -/
  step : σ → Bool → σ × List Bool

namespace ReadMachine

variable {σ : Type*} (m : ReadMachine σ) (x : List Bool)

/-- A configuration: the state and the output so far. -/
structure Cfg (σ : Type*) where
  /-- The state. -/
  state : σ
  /-- The output so far. -/
  out : List Bool

/-- The bit read in state `q`. -/
def readBit (q : σ) : Bool :=
  match m.addr q with
  | some a => x.getD a false
  | none => false

/-- One step on the input `x`; halting configurations are fixed. -/
def next (c : Cfg σ) : Cfg σ :=
  if m.halt c.state then c
  else
    let r := m.step c.state (m.readBit x c.state)
    ⟨r.1, c.out ++ r.2⟩

/-- The configuration after `n` steps on the input `x`, from `c`. -/
def runFrom (c : Cfg σ) (n : ℕ) : Cfg σ := (m.next x)^[n] c

/-- The configuration after `n` steps on the input `x`. -/
def run (n : ℕ) : Cfg σ := m.runFrom x ⟨m.init, []⟩ n

theorem runFrom_add (c : Cfg σ) (n k : ℕ) :
    m.runFrom x c (n + k) = m.runFrom x (m.runFrom x c n) k := by
  simp only [runFrom, Nat.add_comm n k, Function.iterate_add_apply]

theorem run_add (n k : ℕ) : m.run x (n + k) = m.runFrom x (m.run x n) k :=
  m.runFrom_add x _ n k

theorem runFrom_one (c : Cfg σ) : m.runFrom x c 1 = m.next x c := rfl

theorem runFrom_succ (c : Cfg σ) (n : ℕ) : m.runFrom x c (n + 1) = m.runFrom x (m.next x c) n :=
  Function.iterate_succ_apply _ _ _

/-- A step from a state that is not halting. -/
theorem next_of_not_halt {c : Cfg σ} (h : m.halt c.state = false) :
    m.next x c = ⟨(m.step c.state (m.readBit x c.state)).1,
      c.out ++ (m.step c.state (m.readBit x c.state)).2⟩ := by
  simp [next, h]

/-- Halting configurations are fixed. -/
theorem runFrom_of_halt {c : Cfg σ} (h : m.halt c.state = true) (n : ℕ) : m.runFrom x c n = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runFrom_succ, show m.next x c = c by simp [next, h], ih]

/-- After halting, the configuration stays. -/
theorem run_eq_of_halt {n n' : ℕ} (h : m.halt (m.run x n).state = true) (hn : n ≤ n') :
    m.run x n' = m.run x n := by
  rw [show n' = n + (n' - n) by omega, run_add, runFrom_of_halt _ _ h]

/-- **A loop of a read machine**: if from the state `s i` the machine steps to `s (i + 1)` and
emits `e i`, for `i < M`, then after `j ≤ M` steps from `s 0` it is in `s j`, having emitted
`e 0, …, e (j - 1)`. -/
theorem runFrom_loop (s : ℕ → σ) (e : ℕ → List Bool) {M : ℕ}
    (h : ∀ i < M, m.halt (s i) = false ∧ m.step (s i) (m.readBit x (s i)) = (s (i + 1), e i))
    (out : List Bool) {j : ℕ} (hj : j ≤ M) :
    m.runFrom x ⟨s 0, out⟩ j = ⟨s j, out ++ ((List.range j).map e).flatten⟩ := by
  induction j with
  | zero => simp [runFrom]
  | succ j ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
      next_of_not_halt _ _ (h j (by omega)).1, (h j (by omega)).2]
    simp [List.range_succ]

end ReadMachine

end Turing
