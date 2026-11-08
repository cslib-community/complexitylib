/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Pebbling.Basic
public import Complexity.Computability.Circuit.Program

/-!
# Register evaluation of straight-line programs is black pebbling

A straight-line program `p : Program σ n g` has a computation DAG `p.dag` on its wires: the
argument wires of a gate are the predecessors of that gate, and the inputs are sources. This file
introduces a register machine for `p`. Each wire has its own register; a configuration is the
set of occupied registers together with their contents. A step either loads an input, computes a
gate whose argument registers are all occupied, or frees a register. Evaluation with `s`
registers means that at most `s` registers are ever occupied at once.

Forgetting the contents of the registers turns an evaluation into a black pebbling of `p.dag` with
the same moves, and conversely every black pebbling is an evaluation from any initial register
contents. This is the reading of the pebble game in [Savage1998], Section 10.1, where a pebble
on a vertex means that its value is held in a register, placing a pebble on an input reads it,
placing one on a gate computes it, and removing one erases the value. Inputs occupy registers,
as in that model. A gate's value always goes into a fresh register, the gate's own: there is no
sliding, as in the black pebble game of `Cslib.Pebbling.blackPebbleGame`. Savage also allows the
result to be placed on (or moved to) the register of an argument, and under that rule the
register count of every gate that reads at least one wire is one lower.

## Main definitions

* `Cslib.Circuits.Program.dag`: the computation DAG of a program.
* `Cslib.Circuits.Program.RegisterStep`, `Cslib.Circuits.Program.registerLTS`: register
  evaluation, as a cslib `LTS` with an `s`-register budget.
* `Cslib.Circuits.Program.EvaluatesInRegisters`: some evaluation with `s` registers occupies the
  register of `w`.

## Main results

* `Cslib.Circuits.Program.wellFounded_dag`: the computation DAG is acyclic.
* `Cslib.Circuits.Program.registerLTS_mTr_trace_eq`: correctness; every occupied register holds
  the value `p.trace I x` of its wire.
* `Cslib.Circuits.Program.evaluatesInRegisters_iff_blackPebblable`: `p` evaluates `w` with `s`
  registers exactly when `w` is black-pebblable with `s` pebbles in `p.dag`.
* `Cslib.Circuits.Program.sInf_evaluatesInRegisters`: the least number of registers is the black
  pebbling price.

## References

* [J. E. Savage, *Models of Computation*][Savage1998], Section 10.1.
-/

public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ}

/-- The computation DAG of a straight-line program: the argument wires of a gate are its
predecessors, and the inputs are sources. -/
def Program.dag (p : Program σ n g) : Digraph (Wire n g) where
  Adj u v := ∃ (j : Fin g) (k : Fin (σ.Arity (p.lines j).op)), v = .gate j ∧ (p.lines j).wires k = u

theorem Program.dag_adj {p : Program σ n g} {u v : Wire n g} :
    p.dag.Adj u v ↔ ∃ (j : Fin g) (k : Fin (σ.Arity (p.lines j).op)),
      v = .gate j ∧ (p.lines j).wires k = u := Iff.rfl

@[simp] theorem Program.dag_adj_gate {p : Program σ n g} {u : Wire n g} {j : Fin g} :
    p.dag.Adj u (.gate j) ↔ ∃ k, (p.lines j).wires k = u := by
  constructor
  · rintro ⟨j', k, hj, rfl⟩
    cases hj
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨j, k, rfl, rfl⟩

@[simp] theorem Program.not_dag_adj_input (p : Program σ n g) (u : Wire n g) (i : Fin n) :
    ¬ p.dag.Adj u (.input i) := by
  rintro ⟨j, k, hj, -⟩
  cases hj

/-- The computation DAG of a program is acyclic: every wire is accessible, by induction along
the program order. -/
theorem Program.wellFounded_dag (p : Program σ n g) : WellFounded p.dag.Adj :=
  ⟨p.wire_induction (fun _ => ⟨_, fun _ ⟨_, _, h, _⟩ => nomatch h⟩)
    fun j ih => ⟨_, fun _ hu => by obtain ⟨k, rfl⟩ := Program.dag_adj_gate.1 hu; exact ih k⟩⟩

end Cslib.Circuits

namespace Cslib.Circuits

open Cslib.Pebbling

variable {σ : Signature} {n g : ℕ} {U : Type*}

/-- One step of register evaluation of `p`. A configuration is the set of occupied registers,
one per wire, and their contents. Loading an input reads it, computing a gate requires its
argument wires to be held, and any register can be freed. A computed gate value goes into a fresh
register (no sliding onto an argument's register), so register counts at gates that read at
least one wire are one higher than under Savage's sliding rule. -/
inductive Program.RegisterStep (p : Program σ n g) (I : Interpretation σ U) (x : Fin n → U) :
    Finset (Wire n g) × (Wire n g → U) → Move (Wire n g) →
      Finset (Wire n g) × (Wire n g → U) → Prop where
  /-- Load an input into its register. -/
  | load {C : Finset (Wire n g)} {r : Wire n g → U} (i : Fin n) :
      Program.RegisterStep p I x (C, r) (.place (.input i))
        (insert (.input i) C, Function.update r (.input i) (x i))
  /-- Compute a gate from the held registers of its argument wires, into the gate's own fresh
register. -/
  | compute {C : Finset (Wire n g)} {r : Wire n g → U} (j : Fin g)
      (h : ∀ k, (p.lines j).wires k ∈ C) :
      Program.RegisterStep p I x (C, r) (.place (.gate j))
        (insert (.gate j) C, Function.update r (.gate j) (I (p.lines j).op (r ∘ (p.lines j).wires)))
  /-- Free a register. -/
  | free {C : Finset (Wire n g)} {r : Wire n g → U} (w : Wire n g) :
      Program.RegisterStep p I x (C, r) (.remove w) (C.erase w, r)

/-- Register evaluation of `p` with at most `s` occupied registers. -/
def Program.registerLTS (p : Program σ n g) (I : Interpretation σ U) (x : Fin n → U) (s : ℕ) :
    LTS (Finset (Wire n g) × (Wire n g → U)) (Move (Wire n g)) where
  Tr c m d := p.RegisterStep I x c m d ∧ d.1.card ≤ s

theorem Program.registerLTS_tr {p : Program σ n g} {I : Interpretation σ U} {x : Fin n → U}
    {s : ℕ} {c d : Finset (Wire n g) × (Wire n g → U)} {m : Move (Wire n g)} :
    (p.registerLTS I x s).Tr c m d ↔ p.RegisterStep I x c m d ∧ d.1.card ≤ s := Iff.rfl

end Cslib.Circuits

namespace Cslib.Circuits

open Cslib.Pebbling

variable {σ : Signature} {n g : ℕ} {U : Type*}
variable {p : Program σ n g} {I : Interpretation σ U} {x : Fin n → U}

/-- **Correctness.** A step keeps every occupied register equal to the value of its wire. -/
theorem Program.RegisterStep.trace_eq {c d : Finset (Wire n g) × (Wire n g → U)}
    {m : Move (Wire n g)} (h : p.RegisterStep I x c m d)
    (hc : ∀ w ∈ c.1, c.2 w = p.trace I x w) : ∀ w ∈ d.1, d.2 w = p.trace I x w := by
  cases h with
  | @load C r i =>
    intro w hw
    dsimp only at hw hc ⊢
    by_cases hwi : w = .input i
    · subst hwi
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hwi]
      exact hc w ((Finset.mem_insert.1 hw).resolve_left hwi)
  | @compute C r j hj =>
    intro w hw
    dsimp only at hw hc ⊢
    by_cases hwj : w = .gate j
    · subst hwj
      rw [Function.update_self]
      have hargs : r ∘ (p.lines j).wires = p.trace I x ∘ (p.lines j).wires :=
        funext fun k => hc _ (hj k)
      rw [hargs]
      exact p.lines_eval I x j
    · rw [Function.update_of_ne hwj]
      exact hc w ((Finset.mem_insert.1 hw).resolve_left hwj)
  | free w => exact fun v hv => hc v (Finset.mem_of_mem_erase hv)

theorem Program.registerLTS_mTr_trace_eq {s : ℕ} {c d : Finset (Wire n g) × (Wire n g → U)}
    {ms : List (Move (Wire n g))} (h : (p.registerLTS I x s).MTr c ms d)
    (hc : ∀ w ∈ c.1, c.2 w = p.trace I x w) : ∀ w ∈ d.1, d.2 w = p.trace I x w := by
  induction h with
  | refl => exact hc
  | stepL h _ ih => exact ih (h.1.trace_eq hc)

/-- Forgetting register contents turns a register evaluation into a black pebbling of the
computation DAG. -/
theorem Program.RegisterStep.blackStep {c d : Finset (Wire n g) × (Wire n g → U)}
    {m : Move (Wire n g)} (h : p.RegisterStep I x c m d) : BlackStep p.dag c.1 m d.1 := by
  cases h with
  | load i => exact .place fun u hu => absurd hu (p.not_dag_adj_input u i)
  | compute j hj =>
    refine .place fun u hu => ?_
    obtain ⟨k, rfl⟩ := Program.dag_adj_gate.1 hu
    exact hj k
  | free w => exact .remove

theorem Program.blackPebbleGame_mTr_of_registerLTS {s : ℕ}
    {c d : Finset (Wire n g) × (Wire n g → U)} {ms : List (Move (Wire n g))}
    (h : (p.registerLTS I x s).MTr c ms d) : (blackPebbleGame p.dag s).MTr c.1 ms d.1 := by
  induction h with
  | refl => exact .refl
  | stepL h _ ih => exact .stepL ⟨h.1.blackStep, h.2⟩ ih

/-- Every black pebbling of the computation DAG is a register evaluation, from any initial
register contents. -/
theorem Program.exists_registerLTS_mTr {s : ℕ} {C D : Finset (Wire n g)}
    {ms : List (Move (Wire n g))} (h : (blackPebbleGame p.dag s).MTr C ms D)
    (r : Wire n g → U) : ∃ r', (p.registerLTS I x s).MTr (C, r) ms (D, r') := by
  induction h generalizing r with
  | refl => exact ⟨r, .refl⟩
  | @stepL C₁ m C₂ ms C₃ hstep _ ih =>
    obtain ⟨hstep, hcard⟩ := hstep
    cases hstep with
    | @place w hw =>
      cases w with
      | input i =>
        obtain ⟨r', hr'⟩ := ih (Function.update r (.input i) (x i))
        exact ⟨r', .stepL ⟨.load i, hcard⟩ hr'⟩
      | gate j =>
        obtain ⟨r', hr'⟩ := ih _
        exact ⟨r', .stepL ⟨.compute j fun k => hw _ (Program.dag_adj_gate.2 ⟨k, rfl⟩), hcard⟩ hr'⟩
    | @remove w =>
      obtain ⟨r', hr'⟩ := ih r
      exact ⟨r', .stepL ⟨.free w, hcard⟩ hr'⟩

/-- `p` evaluates wire `w` with at most `s` registers, from the initial contents `r₀`. -/
def Program.EvaluatesInRegisters (p : Program σ n g) (I : Interpretation σ U) (x : Fin n → U)
    (r₀ : Wire n g → U) (s : ℕ) (w : Wire n g) : Prop :=
  ∃ ms d, (p.registerLTS I x s).MTr (∅, r₀) ms d ∧ w ∈ d.1

/-- A register evaluation that reaches `w` holds the correct value of `w`. -/
theorem Program.EvaluatesInRegisters.exists_eq_trace {r₀ : Wire n g → U} {s : ℕ} {w : Wire n g}
    (h : p.EvaluatesInRegisters I x r₀ s w) :
    ∃ ms d, (p.registerLTS I x s).MTr (∅, r₀) ms d ∧ w ∈ d.1 ∧ d.2 w = p.trace I x w := by
  obtain ⟨ms, d, hd, hw⟩ := h
  exact ⟨ms, d, hd, hw, Program.registerLTS_mTr_trace_eq hd
    (fun v hv => absurd hv (Finset.notMem_empty v)) w hw⟩

/-- **Registers are pebbles.** `p` evaluates `w` with `s` registers exactly when `w` can be
black-pebbled with `s` pebbles in the computation DAG of `p`, for every interpretation, input
and initial register contents. -/
theorem Program.evaluatesInRegisters_iff_blackPebblable {r₀ : Wire n g → U} {s : ℕ}
    {w : Wire n g} : p.EvaluatesInRegisters I x r₀ s w ↔ BlackPebblable p.dag s w := by
  constructor
  · rintro ⟨ms, d, hd, hw⟩
    exact ⟨ms, d.1, Program.blackPebbleGame_mTr_of_registerLTS hd, hw⟩
  · rintro ⟨ms, D, hD, hw⟩
    obtain ⟨r', hr'⟩ := Program.exists_registerLTS_mTr (I := I) (x := x) hD r₀
    exact ⟨ms, (D, r'), hr', hw⟩

/-- The least number of registers that evaluates `w` is the black pebbling price of `w` in the
computation DAG. -/
theorem Program.sInf_evaluatesInRegisters (r₀ : Wire n g → U) (w : Wire n g) :
    sInf {s | p.EvaluatesInRegisters I x r₀ s w} = blackPebblingPrice p.dag w := by
  simp only [Program.evaluatesInRegisters_iff_blackPebblable]
  have hne : BlackPebblable p.dag (Fintype.card (Wire n g)) w :=
    blackPebblable_fintypeCard p.wellFounded_dag w
  exact le_antisymm (Nat.sInf_le (blackPebblable_blackPebblingPrice hne))
    (blackPebblingPrice_le (Nat.sInf_mem (s := {s | BlackPebblable p.dag s w}) ⟨_, hne⟩))

/-- Every wire can be evaluated with one register per wire. -/
theorem Program.evaluatesInRegisters_card (r₀ : Wire n g → U) (w : Wire n g) :
    p.EvaluatesInRegisters I x r₀ (n + g) w := by
  rw [Program.evaluatesInRegisters_iff_blackPebblable, ← Wire.card]
  exact blackPebblable_fintypeCard p.wellFounded_dag w

end Cslib.Circuits
