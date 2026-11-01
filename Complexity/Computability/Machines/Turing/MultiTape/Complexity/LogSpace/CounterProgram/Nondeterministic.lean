/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler
import Mathlib.Data.List.GetD

/-!
# Nondeterministic counter programs

A counter program (`Turing.CounterProgram`) runs **nondeterministically** when register `0`
receives a fresh nondeterministic bit after every step
(`Turing.CounterProgram.toNondeterministicQueryMachine`): an instruction branches on the bit by
comparing register `0` with `1`. The rest of a step is the deterministic one; in particular the
first instruction sees register `0` at `0`. A branch accepts when it halts with the final word
`[true]`.

A program that halts on every branch of every encoded input `enc a` within `time a` steps, whose
registers stay at most `(n + 1) ^ d` on every branch, where `n` is the length of the input,
decides in logarithmic space the problem of the inputs it accepts
(`Turing.CounterProgram.exists_decidesInLogSpace`): one finite-state nondeterministic machine
decides it within space `c * (Nat.log2 n + 1)`, every branch halting
(`Turing.MultiTapeNTM.DecidesInSpace`). This is the classical description of nondeterministic
logarithmic-space algorithms, a constant number of polynomially bounded counters and random
read-only access to the input [Sipser, Section 8.4][Sipser2013]. The machine is compiled through
`Turing.NondeterministicQueryMachine.exists_decidesInSpace`.

Halting on every branch and the register bounds are established together from an invariant and
a rank that every step from a running configuration satisfying the invariant decreases, whatever
the choice (`Turing.CounterProgram.haltsWithin_of_rank`,
`Turing.CounterProgram.forall_run_of_rank`). Accepting branches are built step by step
(`Turing.CounterProgram.Branches`).

## Main definitions

* `Turing.CounterProgram.withChoice`: overwrite register `0` by a choice bit.
* `Turing.CounterProgram.toNondeterministicQueryMachine`: a counter program as a nondeterministic
  query machine.
* `Turing.CounterProgram.Branches`: some branch leads from one configuration to another.

## Main results

* `Turing.CounterProgram.step_toNondeterministicQueryMachine`: a nondeterministic step is a
  deterministic step followed by a choice.
* `Turing.CounterProgram.haltsWithin_of_rank`, `Turing.CounterProgram.forall_run_of_rank`:
  halting on every branch and invariants of every branch, from a decreasing rank.
* `Turing.CounterProgram.accepts_of_branches`: a branch to the accepting halt accepts.
* `Turing.CounterProgram.exists_decidesInLogSpace`: nondeterministic counter programs with
  polynomially bounded registers decide in logarithmic space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

namespace Turing

namespace CounterProgram

variable (P : CounterProgram) (w : List Bool)

/-- Overwrite register `0` by the choice bit, `1` for `true` and `0` for `false`. -/
def withChoice (s : Config) (choice : Bool) : Config := (s.1, s.2.set 0 choice.toNat)

/-- A counter program as a nondeterministic query machine: a step is a deterministic step, after
which register `0` receives the choice. A halted branch accepts when its final word is
`[true]`. -/
def toNondeterministicQueryMachine : NondeterministicQueryMachine Config where
  init := P.init
  query := P.query
  next p := withChoice (P.exec p.1 p.2.1) p.2.2
  halted := P.halted
  accept s := decide (P.finish s = [true])

/-- **A nondeterministic step** is a deterministic step followed by a choice; halted
configurations stay put. -/
theorem step_toNondeterministicQueryMachine (s : Config) (choice : Bool) :
    P.toNondeterministicQueryMachine.step w s choice =
      if P.halted s = true then s else withChoice (P.step w s) choice := by
  by_cases h : P.halted s = true <;>
    simp [NondeterministicQueryMachine.step, toNondeterministicQueryMachine,
      NondeterministicQueryMachine.read, step_eq, h]

@[simp]
theorem withChoice_fst (s : Config) (choice : Bool) : (withChoice s choice).1 = s.1 := rfl

@[simp]
theorem withChoice_snd (s : Config) (choice : Bool) :
    (withChoice s choice).2 = s.2.set 0 choice.toNat := rfl

/-! ### Every branch -/

section Rank

variable {P w} (Inv : Config → Prop) (rank : Config → ℕ)

/-- An invariant preserved by every step from a running configuration holds of every
configuration on every branch, halted configurations staying put. -/
theorem forall_replay_of_inv
    (hstep : ∀ s, Inv s → P.halted s = false → ∀ choice, Inv (withChoice (P.step w s) choice))
    (choices : List Bool) {s : Config} (hs : Inv s) :
    Inv (P.toNondeterministicQueryMachine.replay w choices s) := by
  induction choices generalizing s with
  | nil => exact hs
  | cons choice choices ih =>
    rw [NondeterministicQueryMachine.replay_cons, step_toNondeterministicQueryMachine]
    split_ifs with h
    · exact ih hs
    · exact ih (hstep s hs (Bool.eq_false_iff.mpr h) choice)

/-- **An invariant of every branch**, from an invariant of the initial configuration preserved by
every step from a running configuration. -/
theorem forall_run_of_rank (hinit : Inv P.init)
    (hstep : ∀ s, Inv s → P.halted s = false → ∀ choice, Inv (withChoice (P.step w s) choice))
    (choices : List Bool) : Inv (P.toNondeterministicQueryMachine.run w choices) :=
  forall_replay_of_inv Inv hstep choices hinit

/-- **Every branch halts within the rank of the initial configuration**, when every step from a
running configuration satisfying an invariant preserves it and decreases the rank, whatever the
choice. -/
theorem haltsWithin_of_rank (hinit : Inv P.init)
    (hstep : ∀ s, Inv s → P.halted s = false → ∀ choice,
      Inv (withChoice (P.step w s) choice) ∧ rank (withChoice (P.step w s) choice) < rank s) :
    P.toNondeterministicQueryMachine.HaltsWithin w (rank P.init) := by
  have key : ∀ (choices : List Bool) (s : Config), Inv s → rank s ≤ choices.length →
      P.halted (P.toNondeterministicQueryMachine.replay w choices s) = true := by
    intro choices
    induction choices with
    | nil =>
      intro s hs hr
      by_contra h
      have := (hstep s hs (Bool.eq_false_iff.mpr h) false).2
      simp only [List.length_nil, Nat.le_zero] at hr
      omega
    | cons choice choices ih =>
      intro s hs hr
      rw [NondeterministicQueryMachine.replay_cons, step_toNondeterministicQueryMachine]
      split_ifs with h
      · exact (P.toNondeterministicQueryMachine.replay_of_halted w h choices).symm ▸ h
      · have h' := hstep s hs (Bool.eq_false_iff.mpr h) choice
        exact ih _ h'.1 (by simp only [List.length_cons] at hr; omega)
  intro choices hlen
  exact key choices P.init hinit hlen.ge

end Rank

/-! ### Some branch -/

variable {P w}

/-- Some branch leads from `s` to `s'`. -/
def Branches (s s' : Config) : Prop :=
  ∃ choices, P.toNondeterministicQueryMachine.replay w choices s = s'

namespace Branches

variable {s s' s'' : Config}

theorem refl (s : Config) : Branches (P := P) (w := w) s s := ⟨[], rfl⟩

theorem trans (h : Branches (P := P) (w := w) s s') (h' : Branches (P := P) (w := w) s' s'') :
    Branches (P := P) (w := w) s s'' := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c ++ c', NondeterministicQueryMachine.replay_append _ _ _ _ _⟩

/-- One step from a running configuration, with either choice. -/
theorem single (hs : P.halted s = false) (choice : Bool) :
    Branches (P := P) (w := w) s (withChoice (P.step w s) choice) :=
  ⟨[choice], by
    rw [NondeterministicQueryMachine.replay_cons, step_toNondeterministicQueryMachine]
    simp [hs]⟩

theorem head (hs : P.halted s = false) (choice : Bool)
    (h : Branches (P := P) (w := w) (withChoice (P.step w s) choice) s') :
    Branches (P := P) (w := w) s s' :=
  (single hs choice).trans h

end Branches

/-- **A branch to the accepting halt accepts.** -/
theorem accepts_of_branches {s : Config} (h : Branches (P := P) (w := w) P.init s)
    (hs : P.instr s.1 = .accept) : P.toNondeterministicQueryMachine.Accepts w := by
  obtain ⟨choices, hrun⟩ := h
  refine ⟨choices, ?_, ?_⟩
  · change P.halted (P.toNondeterministicQueryMachine.replay w choices P.init) = true
    rw [hrun, halted, hs]
    rfl
  · change decide (P.finish (P.toNondeterministicQueryMachine.replay w choices P.init) = [true])
      = true
    rw [hrun, finish, hs]
    rfl

/-- An accepting branch ends at a halt with the final word `[true]`. -/
theorem instr_of_accepts {choices : List Bool}
    (hhalt : P.toNondeterministicQueryMachine.halted (P.toNondeterministicQueryMachine.run w
      choices) = true)
    (hacc : P.toNondeterministicQueryMachine.accept (P.toNondeterministicQueryMachine.run w
      choices) = true) :
    P.instr (P.toNondeterministicQueryMachine.run w choices).1 = .accept := by
  change P.halted _ = true at hhalt
  change decide (P.finish _ = [true]) = true at hacc
  rw [decide_eq_true_eq] at hacc
  unfold halted at hhalt
  unfold finish at hacc
  revert hhalt hacc
  cases P.instr (P.toNondeterministicQueryMachine.run w choices).1 <;>
    simp [Instr.halts, Instr.finish]

/-! ### Logarithmic space -/

section LogSpace

open MultiTapeTM ComputableInSpace Simulation

/-- Overwriting register `0` by a choice is computed in linear space. -/
private theorem withChoice_inSpace :
    ComputableInSpace (fun q : Config × Bool => withChoice q.1 q.2)
      (encPair encConfig encBool) encConfig fun q => (encPair encConfig encBool q).length := by
  have hs : ComputableInSpace (fun q : Config × Bool => q.1) (encPair encConfig encBool)
      encConfig fun q => (encPair encConfig encBool q).length := fst _ _
  have hregs : ComputableInSpace (fun q : Config × Bool => q.1.2)
      (encPair encConfig encBool) (encList encNat)
      fun q => (encPair encConfig encBool q).length :=
    budget_comp_lin (snd _ _) (.refl _) hs
  have hv := budget_prod hregs (budget_prod (budget_const (encB := encNat) 0 (.refl _))
    (budget_finite (encC := encNat) Bool.toNat (snd encConfig encBool)))
  exact budget_prod (budget_comp_lin (fst _ _) (.refl _) hs)
    (budget_comp ComputableInSpace.set hv
      (.const_mul 128 (.add hv.length_le (.const 1 _))))

/-- The transition of the nondeterministic query machine is computed in linear space. -/
private theorem next_inSpace :
    ComputableInSpace (fun p : Config × Option Bool × Bool => withChoice (P.exec p.1 p.2.1)
      p.2.2) (encPair encConfig (encPair (encOption encBool) encBool)) encConfig
      fun p => (encPair encConfig (encPair (encOption encBool) encBool) p).length := by
  have hrest : ComputableInSpace (fun p : Config × Option Bool × Bool => p.2)
      (encPair encConfig (encPair (encOption encBool) encBool))
      (encPair (encOption encBool) encBool)
      fun p => (encPair encConfig (encPair (encOption encBool) encBool) p).length := snd _ _
  have hread : ComputableInSpace (fun p : Config × Option Bool × Bool => (p.1, p.2.1))
      (encPair encConfig (encPair (encOption encBool) encBool)) encConfigRead
      fun p => (encPair encConfig (encPair (encOption encBool) encBool) p).length :=
    budget_prod (fst _ _) (budget_comp_lin (fst _ _) (.refl _) hrest)
  have hexec := budget_comp_linear (g := fun x : Config × Option Bool => P.exec x.1 x.2)
    (exec_inSpace (P := P)) hread
  have hchoice := budget_comp_lin (g := fun q : Option Bool × Bool => q.2) (snd _ _) (.refl _)
    hrest
  have h := budget_comp_linear (g := fun q : Config × Bool => withChoice q.1 q.2)
    withChoice_inSpace (budget_prod hexec hchoice)
  exact h.of_enc_eq fun _ => rfl

/-- The acceptance test of the nondeterministic query machine is computed in linear space. -/
private theorem accept_inSpace :
    ComputableInSpace P.toNondeterministicQueryMachine.accept encConfig encBool
      fun s => (encConfig s).length :=
  dispatch P.code (.halt []) (fun i _ => decide (i.finish = [true]))
    (fun _ => budget_const _ (.refl _)) (fst _ _)

/-- The labels of every branch are bounded by the largest label of the program, and the number of
registers is fixed. -/
private theorem replay_fst_le_and_length (choices : List Bool) {s : Config}
    (hs : s.1 ≤ P.maxLabel ∧ s.2.length = P.registers) :
    (P.toNondeterministicQueryMachine.replay w choices s).1 ≤ P.maxLabel ∧
      (P.toNondeterministicQueryMachine.replay w choices s).2.length = P.registers := by
  refine forall_replay_of_inv (fun s : Config => s.1 ≤ P.maxLabel ∧ s.2.length = P.registers)
    (fun s hs hh choice => ⟨?_, ?_⟩) choices hs
  · have hh' : (P.instr s.1).halts = false := hh
    rw [withChoice_fst, step_eq, hh]
    simp only [Bool.false_eq_true, ↓reduceIte, exec]
    refine (Instr.exec_fst_le hh' _ _).trans ?_
    rcases lt_or_ge s.1 P.code.length with hlt | hge
    · rw [instr, List.getD_eq_getElem _ _ hlt]
      exact le_listMax (List.getElem_mem hlt)
    · rw [instr, List.getD_eq_default _ _ hge] at hh'
      simp [Instr.halts] at hh'
  · rw [withChoice_snd, List.length_set, step_eq, hh]
    simp only [Bool.false_eq_true, ↓reduceIte, exec, Instr.exec_snd_length, hs.2]

/-- **Nondeterministic counter programs decide in logarithmic space.** Let a counter program, run
nondeterministically, halt on every branch on every encoded input `enc a` within `time a` steps,
let its registers stay at most `(n + 1) ^ d` on every branch, where `n` is the length of the
input, and let it accept exactly the inputs of the instances in `A`. Then one finite-state
nondeterministic machine decides `A` within space `c * (Nat.log2 n + 1)`, halting on every
branch. -/
theorem exists_decidesInLogSpace (P : CounterProgram) {α : Type} {enc : α ↪ List Bool}
    {A : Set α} (time : α → ℕ) (d : ℕ)
    (hhalt : ∀ a, P.toNondeterministicQueryMachine.HaltsWithin (enc a) (time a))
    (hbound : ∀ a choices, ∀ r ∈ (P.toNondeterministicQueryMachine.run (enc a) choices).2,
      r ≤ ((enc a).length + 1) ^ d)
    (hA : ∀ a, a ∈ A ↔ P.toNondeterministicQueryMachine.Accepts (enc a)) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      ntm.DecidesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1) := by
  have hnext : ComputableInSpace P.toNondeterministicQueryMachine.next
      (encPair encConfig (encPair (encOption encBool) encBool)) encConfig
      fun p => (encPair encConfig (encPair (encOption encBool) encBool) p).length :=
    next_inSpace (P := P)
  refine P.toNondeterministicQueryMachine.exists_decidesInSpace (encS := encConfig)
    (query_inSpace (P := P)) hnext (halted_inSpace (P := P))
    (accept_inSpace (P := P)) time hhalt hA (fun a => Nat.log2 (enc a).length + 1)
    (fun _ => le_rfl)
    ⟨2 * (encNat P.maxLabel).length + 1 + P.registers * (2 * d + 3), fun a choices => ?_⟩
  have hinit : P.init.1 ≤ P.maxLabel ∧ P.init.2.length = P.registers :=
    ⟨Nat.zero_le _, List.length_replicate⟩
  have h := replay_fst_le_and_length (P := P) (w := enc a) choices hinit
  exact length_encConfig_le P h.1 h.2 (hbound a choices)

end LogSpace

end CounterProgram

end Turing
