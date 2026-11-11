/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Alternating

/-!
# Space-bounded alternating machines

An alternating machine (`Turing.MultiTapeATM`) is bounded in space as its steps are those of the
nondeterministic machine of its table (`Turing.MultiTapePTM.toNTM`). The machine recognizes `A`
within space `s` (`Turing.MultiTapeATM.RecognizesInSpace`) when on every encoded instance `enc a`
every computation path of that nondeterministic machine visits at most `s a` work-tape cells
(`Turing.MultiTapeNTM.RunsInSpace`), and `a ∈ A` exactly when the alternating machine accepts
`enc a` (`Turing.MultiTapeATM.Accepts`). This is the space bound of Chandra, Kozen and Stockmeyer
[Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]: every configuration reachable from the
initial one obeys it. Branches need not halt. Acceptance is the least fixed point
of the labelling, so an infinite branch never helps a configuration accept.

The machine decides `A` within space `s` (`Turing.MultiTapeATM.DecidesInSpace`) when moreover every
branch halts: on every encoded instance some number of steps bounds every computation path, as in
`Turing.MultiTapeNTM.DecidesInSpace` [Sipser, Section 10.3][Sipser2013]. A decider within time `t`
decides within space `k * (t + 1)` (`Turing.MultiTapeATM.DecidesInTime.decidesInSpace`).

## Main definitions

* `Turing.MultiTapeATM.RecognizesInSpace`: recognizing a problem within a space bound.
* `Turing.MultiTapeATM.DecidesInSpace`: deciding a problem within a space bound.

## Main results

* `Turing.MultiTapeATM.DecidesInSpace.recognizesInSpace`: a decider is a recognizer.
* `Turing.MultiTapeATM.RecognizesInSpace.mono`, `Turing.MultiTapeATM.DecidesInSpace.mono`: space
  bounds can be increased.
* `Turing.MultiTapeATM.DecidesInTime.decidesInSpace`: a decider within time `t` decides within
  space `k * (t + 1)`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 10.3][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeATM

variable {k : ℕ} {State : Type} {α : Type}

/-- `atm` recognizes `A` within space `s` relative to the encoding `enc`: on every encoded
instance `enc a`, every computation path of the nondeterministic machine of its table visits at
most `s a` work-tape cells, and `a ∈ A` exactly when `atm` accepts `enc a`
[Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]. No time bound is imposed:
a branch may run forever, and acceptance, the least fixed point of the labelling, never relies on
an infinite branch. -/
def RecognizesInSpace (atm : MultiTapeATM k Bool State) (enc : α ↪ List Bool) (A : Set α)
    (s : α → ℕ) : Prop :=
  ∀ a, atm.toPTM.toNTM.RunsInSpace (enc a) (s a) ∧ (a ∈ A ↔ atm.Accepts (enc a))

/-- `atm` decides `A` within space `s` relative to the encoding `enc`: it recognizes `A` within
space `s`, and every branch halts: on every encoded instance some number of steps bounds every
computation path. -/
def DecidesInSpace (atm : MultiTapeATM k Bool State) (enc : α ↪ List Bool) (A : Set α)
    (s : α → ℕ) : Prop :=
  atm.RecognizesInSpace enc A s ∧ ∀ a, ∃ t, atm.toPTM.toNTM.RunsInTime (enc a) t

variable {atm : MultiTapeATM k Bool State} {enc : α ↪ List Bool} {A : Set α}

/-- A decider within space `s` recognizes its problem within space `s`. -/
theorem DecidesInSpace.recognizesInSpace {s : α → ℕ} (h : atm.DecidesInSpace enc A s) :
    atm.RecognizesInSpace enc A s :=
  h.1

/-- Space bounds can be increased. -/
theorem RecognizesInSpace.mono {s s' : α → ℕ} (h : atm.RecognizesInSpace enc A s)
    (hs : ∀ a, s a ≤ s' a) : atm.RecognizesInSpace enc A s' :=
  fun a => ⟨(h a).1.mono (hs a), (h a).2⟩

/-- Space bounds can be increased. -/
theorem DecidesInSpace.mono {s s' : α → ℕ} (h : atm.DecidesInSpace enc A s)
    (hs : ∀ a, s a ≤ s' a) : atm.DecidesInSpace enc A s' :=
  ⟨h.1.mono hs, h.2⟩

/-- **Space is at most time.** A decider within time `t` decides within space `k * (t + 1)`. -/
theorem DecidesInTime.decidesInSpace {t : α → ℕ} (h : atm.DecidesInTime enc A t) :
    atm.DecidesInSpace enc A fun a => k * (t a + 1) :=
  ⟨fun a => ⟨(h a).1.runsInSpace, (h a).2⟩, fun a => ⟨t a, (h a).1⟩⟩

end Turing.MultiTapeATM
