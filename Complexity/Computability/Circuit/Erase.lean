/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.InnerSize
import Complexity.Computability.Circuit.Program

/-!
# Replacing gates by constants

The signature `σ.withConstants P` is `σ` with a constant, an operation of arity zero, for every
element of `P`, and `I.withConstants γ` interprets the constant `k` as `γ k`. Replacing gates of
a program by constants (`Program.replaceGates`) keeps the shape of the program: the gate `g`
becomes the constant `k` when `r g = some k`, and keeps its line when `r g = none`.

*Erasing* a set of *special* gates (`Program.eraseGates`) replaces each special gate `g` by a
constant named after `g` itself, in `σ.withConstants {g // special g}`. The inner gates of the
erased program are the inner gates that are not special (`Program.innerGates_eraseGates`), and
its fan-in is that of the other gates (`Program.fanInAtMost_eraseGates_iff`). When the constants
hold the values of the special gates in a run of the original program, the erased program has the
same run (`Program.trace_eraseGates`). So a program with a few gates of unbounded fan-in is a
program of bounded fan-in, once the values of those gates are given.

## Main definitions

* `Cslib.Circuits.Signature.withConstants`, `Cslib.Circuits.Interpretation.withConstants`: a
  signature and an interpretation with constants added.
* `Cslib.Circuits.Line.const`, `Cslib.Circuits.Line.liftConstants`: constant lines and lifted lines
  over `σ.withConstants P`.
* `Cslib.Circuits.Program.replaceGates`: replacing some gates by constants.
* `Cslib.Circuits.Program.eraseGates`: replacing the special gates by constants named after them.

## Main results

* `Cslib.Circuits.Program.lines_eraseGates`: the lines of the erased program.
* `Cslib.Circuits.Program.innerGates_eraseGates`: its inner gates are the ordinary inner gates.
* `Cslib.Circuits.Program.fanInAtMost_eraseGates_iff`: its fan-in is that of the ordinary gates.
* `Cslib.Circuits.Program.trace_eraseGates_gate`, `Cslib.Circuits.Program.trace_eraseGates`: its
  run, and the run with the true values of the special gates.
-/

@[expose] public section

namespace Cslib.Circuits

universe v w

variable {σ : Signature.{v}} {n s : ℕ} {U : Type*} {P : Type w}

/-! ### Constants -/

/-- The signature `σ` with a constant, an operation of arity zero, for every element of `P`. -/
abbrev Signature.withConstants (σ : Signature.{v}) (P : Type w) : Signature.{max v w} where
  Op := σ.Op ⊕ P
  Arity := Sum.elim σ.Arity fun _ => 0

/-- The interpretation `I`, with the constant `k` holding the value `γ k`. -/
def Interpretation.withConstants (I : Interpretation σ U) (γ : P → U) :
    Interpretation (σ.withConstants P) U
  | .inl o, x => I o x
  | .inr k, _ => γ k

/-- `I.withConstants γ` interprets an original operation `.inl o` using `I`. -/
@[simp] theorem Interpretation.withConstants_inl (I : Interpretation σ U) (γ : P → U) (o : σ.Op)
    (x : Fin (σ.Arity o) → U) : I.withConstants γ (.inl o) x = I o x :=
  rfl

/-- `I.withConstants γ` interprets a constant `.inr k` as `γ k`. -/
@[simp] theorem Interpretation.withConstants_inr (I : Interpretation σ U) (γ : P → U) (k : P)
    (x : Fin 0 → U) : I.withConstants γ (.inr k) x = γ k :=
  rfl

/-- The line of the constant `k`. -/
def Line.const (k : P) : Line (σ.withConstants P) n s :=
  ⟨.inr k, Fin.elim0⟩

/-- A line over `σ`, as a line over the signature with constants. -/
def Line.liftConstants (line : Line σ n s) : Line (σ.withConstants P) n s :=
  ⟨.inl line.op, line.wires⟩

/-- Reindexing the wires of a constant line leaves it unchanged. -/
@[simp] theorem Line.const_mapWires {n' s' : ℕ} (k : P) (f : Wire n s → Wire n' s') :
    (Line.const (σ := σ) k).mapWires f = Line.const k := by
  simp only [Line.const, Line.mapWires]
  congr 1
  funext a
  exact a.elim0

/-- Lifting a line to `σ.withConstants P` commutes with wire reindexing. -/
@[simp] theorem Line.liftConstants_mapWires {n' s' : ℕ} (line : Line σ n s)
    (f : Wire n s → Wire n' s') :
    (line.liftConstants (P := P)).mapWires f = (line.mapWires f).liftConstants :=
  rfl

/-! ### Replacing gates by constants -/

/-- **Replacing gates by constants.** The gate `g` becomes the constant `k` when `r g = some k`,
and keeps its line when `r g = none`. -/
def Program.replaceGates : {s : ℕ} → Program σ n s → (Fin s → Option P) →
    Program (σ.withConstants P) n s
  | _, .empty, _ => .empty
  | _, .gate p line, r => (p.replaceGates fun g => r g.castSucc).gate
      ((r (Fin.last _)).elim line.liftConstants Line.const)

/-- The lines of a program with gates replaced by constants. -/
private theorem Program.lines_replaceGates (p : Program σ n s) (r : Fin s → Option P) (g : Fin s) :
    (p.replaceGates r).lines g = (r g).elim (p.lines g).liftConstants Line.const := by
  induction p with
  | empty => exact g.elim0
  | @gate s p line ih =>
    refine Fin.lastCases ?_ (fun g => ?_) g
    · rw [replaceGates, lines_gate_last, lines_gate_last]
      cases r (Fin.last s) <;> simp
    · rw [replaceGates, lines_gate_castSucc, lines_gate_castSucc, ih]
      cases r g.castSucc <;> simp

/-! ### Erasing the special gates -/

variable (special : Fin s → Prop) [DecidablePred special]

/-- **Erasing the special gates.** Each special gate `g` becomes the constant named `g`, and the
other gates are kept. -/
def Program.eraseGates (p : Program σ n s) : Program (σ.withConstants {g // special g}) n s :=
  p.replaceGates fun g => if h : special g then some ⟨g, h⟩ else none

variable {special}

/-- The lines of an erased program. -/
theorem Program.lines_eraseGates (p : Program σ n s) (g : Fin s) :
    (p.eraseGates special).lines g =
      if h : special g then Line.const ⟨g, h⟩ else (p.lines g).liftConstants := by
  rw [eraseGates, lines_replaceGates]
  split_ifs <;> rfl

private theorem Program.lines_eraseGates_of_special (p : Program σ n s) {g : Fin s}
    (hg : special g) :
    (p.eraseGates special).lines g = Line.const ⟨g, hg⟩ := by
  simp only [lines_eraseGates, hg, ↓reduceDIte]

private theorem Program.lines_eraseGates_of_not_special (p : Program σ n s) {g : Fin s}
    (hg : ¬special g) : (p.eraseGates special).lines g = (p.lines g).liftConstants := by
  simp only [lines_eraseGates, hg, ↓reduceDIte]

/-- The arity of a gate of the erased program: zero for a special gate, and the arity of the
gate otherwise. -/
private theorem Program.arity_lines_eraseGates (p : Program σ n s) (g : Fin s) :
    (σ.withConstants {g // special g}).Arity ((p.eraseGates special).lines g).op =
      if special g then 0 else σ.Arity (p.lines g).op := by
  by_cases hg : special g
  · simp only [lines_eraseGates_of_special p hg, hg, ↓reduceIte]
    rfl
  · simp only [lines_eraseGates_of_not_special p hg, hg, ↓reduceIte]
    rfl

/-- The inner gates of the erased program are the inner gates that are not special. -/
theorem Program.innerGates_eraseGates (p : Program σ n s) :
    (p.eraseGates special).innerGates = p.innerGates.filter fun g => ¬special g := by
  ext g
  rw [Finset.mem_filter, mem_innerGates, mem_innerGates, arity_lines_eraseGates]
  split_ifs <;> tauto

/-- The erased program has fan-in at most `r` exactly when every gate that is not special
does. -/
theorem Program.fanInAtMost_eraseGates_iff {p : Program σ n s} {r : ℕ} :
    (p.eraseGates special).FanInAtMost r ↔ ∀ g, ¬special g → σ.Arity (p.lines g).op ≤ r := by
  rw [fanInAtMost_iff]
  refine forall_congr' fun g => ?_
  rw [arity_lines_eraseGates]
  by_cases hg : special g <;> simp [hg]

variable {I : Interpretation σ U} {γ : {g // special g} → U}

/-- The value of a gate in a run of the erased program: the value of its constant for a special
gate, and the gate applied to the values of its arguments otherwise. -/
theorem Program.trace_eraseGates_gate (p : Program σ n s) (x : Fin n → U) (g : Fin s) :
    (p.eraseGates special).trace (I.withConstants γ) x (.gate g) =
      if h : special g then γ ⟨g, h⟩ else
        I (p.lines g).op fun a => (p.eraseGates special).trace (I.withConstants γ) x
          ((p.lines g).wires a) := by
  rw [trace_gate]
  by_cases hg : special g
  · rw [lines_eraseGates_of_special p hg]
    simp only [hg, ↓reduceDIte]
    rfl
  · rw [lines_eraseGates_of_not_special p hg]
    simp only [hg, ↓reduceDIte]
    rfl

/-- **Erasing gates keeps the run** when the constants hold the values of the special gates in
the run of the original program. -/
theorem Program.trace_eraseGates {p : Program σ n s} {x : Fin n → U}
    (hγ : ∀ g (h : special g), γ ⟨g, h⟩ = p.trace I x (.gate g)) :
    (p.eraseGates special).trace (I.withConstants γ) x = p.trace I x := by
  refine (eq_trace_of_forall_gate (p := p.eraseGates special) (v := p.trace I x)
    (fun _ => rfl) fun g => ?_).symm
  by_cases hg : special g
  · rw [lines_eraseGates_of_special p hg]
    exact (hγ g hg).symm
  · rw [lines_eraseGates_of_not_special p hg]
    exact p.trace_gate I x g

end Cslib.Circuits
