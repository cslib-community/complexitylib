/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Feature
import Mathlib.Data.Fintype.Sum

/-!
# Positive local rules for native deterministic tableaux

The finite collection of tape-feature names is independent of the input and time bound.
`rowStep` computes the next row using only positive occurrences of the preceding row.
In particular, a cell is preserved when a positively witnessed head is elsewhere. This
avoids the negative recursive head test in an ordinary tableau constraint.

The semantics are the native `Turing.MultiTapeTM` configurations and transition function.
These rules are the local part of the machine-to-LFP construction in the proof of the
Immerman–Vardi theorem; they do not assume a machine-to-formula compiler.

## Main definitions

* `Tag`: the finite feature names, with signed work-tape coordinates.
* `row`: the row described by a native configuration.
* `rowStep`: the positive local transition rules.

## Main results

* `rowStep_mono`: monotonicity in every preceding-row fact.

## References

* [N. Immerman, *Relational Queries Computable in Polynomial Time*][Immerman1986], Section 3.
-/

@[expose] public section

namespace Cslib.Complexity.ImmermanVardi.Tableau

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature

/-- The input-independent names of basic features. Unary facts use every coordinate. -/
inductive Tag (m : ℕ) (State : Type) where
  /-- The control state, including the halted state. -/
  | state (q : Option State)
  /-- The finite view of the output word. -/
  | out (o : OutView)
  /-- The position of the input head. -/
  | inPos
  /-- The position of a work head; `true` is the nonnegative orientation. -/
  | head (i : Fin m) (sign : Bool)
  /-- The contents of a signed work cell. -/
  | cell (i : Fin m) (sign : Bool) (s : Option Bool)
  deriving DecidableEq, Fintype

variable {m B : ℕ} {State : Type}

/-- Interpret an oriented coordinate as an integer tape offset. -/
def offset (sign : Bool) (a : Fin B) : ℤ := if sign then a.val else -a.val

/-- The feature named by a tag at the specified coordinate. -/
def Tag.feature : Tag m State → Fin B → Feature m State
  | .state q, _ => .state q
  | .out o, _ => .out o
  | .inPos, a => .inPos a.val
  | .head i sign, a => .head i (offset sign a)
  | .cell i sign s, a => .cell i (offset sign a) s

/-- A row of facts, represented by its positive relation entries. -/
abbrev Row (m : ℕ) (State : Type) (B : ℕ) := Tag m State → Fin B → Prop

/-- The row described by a native machine configuration. -/
def row {input : List Bool} (cfg : Cfg m Bool State input) : Row m State B :=
  fun q a => (q.feature a).Holds cfg

/-- A positive witness for the symbol under a work head. -/
def read (R : Row m State B) (i : Fin m) (s : Option Bool) : Prop :=
  ∃ a, (R (.head i true) a ∧ R (.cell i true s) a) ∨
    (R (.head i false) a ∧ R (.cell i false s) a)

/-- A positive witness for a running situation. -/
def situation (input : List Bool) (R : Row m State B) (y : Situation m State)
    (a : Fin B) : Prop :=
  R (.state (some y.1)) a ∧
    (∃ j, R .inPos j ∧ inputAt input j.val = y.2.1) ∧
    ∀ i, read R i (y.2.2 i)

/-- A head known positively to be somewhere other than the specified signed cell. -/
def elsewhere (R : Row m State B) (i : Fin m) (sign : Bool) (a : Fin B) : Prop :=
  ∃ b, (R (.head i sign) b ∧ b ≠ a) ∨
    (R (.head i (!sign)) b ∧ ¬(b.val = 0 ∧ a.val = 0))

/-- The positive predecessor rule for an input-head movement, including clamped end cells. -/
def inputPrev (input : List Bool) (R : Row m State B) (d : SignType) (a : Fin B) : Prop :=
  match d with
  | .zero => R .inPos a
  | .neg => (a.val = 0 ∧ R .inPos a) ∨ ∃ b, a.val + 1 = b.val ∧ R .inPos b
  | .pos => (a.val ≠ 0 ∧ inputAt input a.val = none ∧ R .inPos a) ∨
      ∃ b, b.val + 1 = a.val ∧ R .inPos b ∧
        (b.val = 0 ∨ inputAt input b.val ≠ none)

/-- The positive predecessor rule for a work-head movement, in the target orientation. -/
def headPrev (R : Row m State B) (i : Fin m) (sign : Bool) (d : SignType)
    (a : Fin B) : Prop :=
  match (if sign then d else -d) with
  | .zero => R (.head i sign) a
  | .neg => ∃ b, a.val + 1 = b.val ∧ R (.head i sign) b
  | .pos =>
      (a.val = 0 ∧ ∃ b, b.val = 1 ∧ R (.head i (!sign)) b) ∨
      ∃ b, b.val + 1 = a.val ∧ R (.head i sign) b

/-- Positive local transition rules for each basic feature. -/
noncomputable def rowStep (tm : MultiTapeTM m Bool State) (input : List Bool)
    (R : Row m State B) : Row m State B
  | .state q, a =>
      (R (.state none) a ∧ q = none) ∨
        ∃ y, (tm.actionOf y).state = q ∧ situation input R y a
  | .out o, a =>
      (R (.state none) a ∧ R (.out o) a) ∨
        ∃ y o', o'.push (tm.actionOf y).output = o ∧
          situation input R y a ∧ R (.out o') a
  | .inPos, a =>
      (R (.state none) a ∧ R .inPos a) ∨
        ∃ y, situation input R y a ∧ inputPrev input R (tm.actionOf y).inputTape a
  | .head i sign, a =>
      (R (.state none) a ∧ R (.head i sign) a) ∨
        ∃ y, situation input R y a ∧ headPrev R i sign ((tm.actionOf y).workTapes i).2 a
  | .cell i sign s, a =>
      (R (.cell i sign s) a ∧ (R (.state none) a ∨ elsewhere R i sign a)) ∨
        ∃ y s', ((tm.actionOf y).workTapes i).1.getD s' = s ∧
          situation input R y a ∧ R (.head i sign) a ∧ R (.cell i sign s') a

private theorem read_mono {R S : Row m State B} (h : ∀ q a, R q a → S q a)
    {i : Fin m} {s : Option Bool} (hr : read R i s) : read S i s := by
  rcases hr with ⟨a, h' | h'⟩
  · exact ⟨a, Or.inl ⟨h _ _ h'.1, h _ _ h'.2⟩⟩
  · exact ⟨a, Or.inr ⟨h _ _ h'.1, h _ _ h'.2⟩⟩

private theorem situation_mono {input : List Bool} {R S : Row m State B}
    (h : ∀ q a, R q a → S q a) {y : Situation m State} {a : Fin B}
    (hr : situation input R y a) : situation input S y a := by
  rcases hr with ⟨hq, ⟨j, hj, hs⟩, hw⟩
  exact ⟨h _ _ hq, ⟨j, h _ _ hj, hs⟩, fun i => read_mono h (hw i)⟩

private theorem elsewhere_mono {R S : Row m State B} (h : ∀ q a, R q a → S q a)
    {i : Fin m} {sign : Bool} {a : Fin B} (hr : elsewhere R i sign a) :
    elsewhere S i sign a := by
  rcases hr with ⟨b, h' | h'⟩
  · exact ⟨b, Or.inl ⟨h _ _ h'.1, h'.2⟩⟩
  · exact ⟨b, Or.inr ⟨h _ _ h'.1, h'.2⟩⟩

private theorem inputPrev_mono {input : List Bool} {R S : Row m State B}
    (h : ∀ q a, R q a → S q a) {d : SignType} {a : Fin B}
    (hr : inputPrev input R d a) : inputPrev input S d a := by
  cases d <;> simp only [inputPrev] at hr ⊢
  · exact h _ _ hr
  · rcases hr with ⟨ha, hr⟩ | ⟨b, hb, hr⟩
    · exact Or.inl ⟨ha, h _ _ hr⟩
    · exact Or.inr ⟨b, hb, h _ _ hr⟩
  · rcases hr with ⟨ha, hb, hr⟩ | ⟨b, hb, hr, hx⟩
    · exact Or.inl ⟨ha, hb, h _ _ hr⟩
    · exact Or.inr ⟨b, hb, h _ _ hr, hx⟩

private theorem headPrev_mono {R S : Row m State B} (h : ∀ q a, R q a → S q a)
    {i : Fin m} {sign : Bool} {d : SignType} {a : Fin B}
    (hr : headPrev R i sign d a) : headPrev S i sign d a := by
  unfold headPrev at hr ⊢
  generalize (if sign then d else -d) = e at hr ⊢
  cases e
  · exact h _ _ hr
  · rcases hr with ⟨b, hb, hr⟩
    exact ⟨b, hb, h _ _ hr⟩
  · rcases hr with ⟨ha, b, hb, hr⟩ | ⟨b, hb, hr⟩
    · exact Or.inl ⟨ha, b, hb, h _ _ hr⟩
    · exact Or.inr ⟨b, hb, h _ _ hr⟩

/-- Every recursive occurrence in the local transition rules is monotone. -/
theorem rowStep_mono (tm : MultiTapeTM m Bool State) (input : List Bool)
    {R S : Row m State B} (h : ∀ q a, R q a → S q a) :
    ∀ q a, rowStep tm input R q a → rowStep tm input S q a := by
  intro q a hr
  cases q with
  | state q =>
    rcases hr with ⟨hq, he⟩ | ⟨y, he, hy⟩
    · exact Or.inl ⟨h _ _ hq, he⟩
    · exact Or.inr ⟨y, he, situation_mono h hy⟩
  | out o =>
    rcases hr with ⟨hq, ho⟩ | ⟨y, o', he, hy, ho⟩
    · exact Or.inl ⟨h _ _ hq, h _ _ ho⟩
    · exact Or.inr ⟨y, o', he, situation_mono h hy, h _ _ ho⟩
  | inPos =>
    rcases hr with ⟨hq, hp⟩ | ⟨y, hy, hp⟩
    · exact Or.inl ⟨h _ _ hq, h _ _ hp⟩
    · exact Or.inr ⟨y, situation_mono h hy, inputPrev_mono h hp⟩
  | head i sign =>
    rcases hr with ⟨hq, hp⟩ | ⟨y, hy, hp⟩
    · exact Or.inl ⟨h _ _ hq, h _ _ hp⟩
    · exact Or.inr ⟨y, situation_mono h hy, headPrev_mono h hp⟩
  | cell i sign s =>
    rcases hr with ⟨hc, hq | he⟩ | ⟨y, s', he, hy, hh, hc⟩
    · exact Or.inl ⟨h _ _ hc, Or.inl (h _ _ hq)⟩
    · exact Or.inl ⟨h _ _ hc, Or.inr (elsewhere_mono h he)⟩
    · exact Or.inr ⟨y, s', he, situation_mono h hy, h _ _ hh, h _ _ hc⟩

end Cslib.Complexity.ImmermanVardi.Tableau
