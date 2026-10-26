/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
public import Complexity.Computability.Machines.Turing.MultiTape.Run
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Correct

/-!
# Halting of machines and of their descriptions

A deterministic multi-tape machine halts on an input when its run from the initial configuration
is halted after some number of steps (`Turing.MultiTapeTM.Halts`). It then halts with exactly one
output (`Turing.MultiTapeTM.Computes.unique`); cslib's `Turing.MultiTapeTM.Computes` records that
output, without a bound on the number of steps. A halted run neither moves nor visits new cells, so
a machine halting with an output computes it within the time at which it halts and the space it
has used by then (`Turing.MultiTapeTM.Computes.exists_computesInTimeAndSpace`).

The same notions for the machines described by a description
(`Turing.MultiTapeTM.Universal.Desc`) are read off the simulation
`Turing.MultiTapeTM.Universal.simulate`, which the universal machine computes: the described machine
halts when the simulation reports a halted run after some number of steps
(`Turing.MultiTapeTM.Universal.Desc.Halts`), with the output collected by then
(`Turing.MultiTapeTM.Universal.Desc.Computes`). On the description of a machine with finitely many
states and symbols they are the notions of the machine itself, under the renaming of its symbols.

## Main definitions

* `Turing.MultiTapeTM.Halts`: a machine halts on an input.
* `Turing.MultiTapeTM.Universal.Desc.Halts`, `Turing.MultiTapeTM.Universal.Desc.Computes`: the
  machine described by a description halts on an input, with a given output.

## Main results

* `Turing.MultiTapeTM.Computes.unique`: a machine halts with at most one output.
* `Turing.MultiTapeTM.halts_iff_exists_computes`: a machine halts exactly when it halts with some
  output.
* `Turing.MultiTapeTM.Computes.exists_computesInTimeAndSpace`: an output computed without bounds is
  computed within some time and space bounds.
* `Turing.MultiTapeTM.Universal.Desc.halts_desc`,
  `Turing.MultiTapeTM.Universal.Desc.computes_desc`: on descriptions of machines, halting and
  outputs are those of the machines.
* `Turing.MultiTapeTM.Universal.Desc.halts_iff_exists_computes`: a described machine halts exactly
  when it halts with some output.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 3.1][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {input : List Symbol}

/-- The machine halts on `input`: its run from the initial configuration is halted after some
number of steps. -/
def Halts (tm : MultiTapeTM k Symbol State) (input : List Symbol) : Prop :=
  ∃ t, (tm.runFrom (tm.initCfg input) t).Halted

/-- A machine that halts with an output halts. -/
theorem Computes.halts {output : List Symbol} (h : tm.Computes input output) : tm.Halts input :=
  let ⟨u, hu, _⟩ := h
  ⟨u, hu⟩

/-- A machine halts with at most one output. -/
theorem Computes.unique {o₁ o₂ : List Symbol} (h₁ : tm.Computes input o₁)
    (h₂ : tm.Computes input o₂) : o₁ = o₂ := by
  obtain ⟨u₁, hu₁, rfl⟩ := h₁
  obtain ⟨u₂, hu₂, rfl⟩ := h₂
  rcases le_total u₁ u₂ with h | h
  · rw [runFrom_eq_of_halt tm _ h hu₁]
  · rw [runFrom_eq_of_halt tm _ h hu₂]

/-- Once halted, a run has the output it halts with. -/
theorem Computes.output_eq_of_halted {output : List Symbol} (h : tm.Computes input output) {t : ℕ}
    (ht : (tm.runFrom (tm.initCfg input) t).Halted) :
    (tm.runFrom (tm.initCfg input) t).output = output :=
  Computes.unique ⟨t, ht, rfl⟩ h

/-- A machine halts exactly when it halts with some output. -/
theorem halts_iff_exists_computes : tm.Halts input ↔ ∃ output, tm.Computes input output :=
  ⟨fun ⟨t, ht⟩ => ⟨_, t, ht, rfl⟩, fun ⟨_, h⟩ => h.halts⟩


namespace Universal

/-- The machine described by `d` halts on the input `x`: the simulation reports a halted run after
some number of steps. -/
def Desc.Halts (d : Desc) (x : List ℕ) : Prop :=
  ∃ t, (simulate d x t).2 = true

/-- The machine described by `d` halts on the input `x` with output `out`. -/
def Desc.Computes (d : Desc) (x : List ℕ) (out : List ℕ) : Prop :=
  ∃ t, simulate d x t = (out, true)

/-- The machine described by `d` halts exactly when it halts with some output. -/
theorem Desc.halts_iff_exists_computes {d : Desc} {x : List ℕ} :
    d.Halts x ↔ ∃ o, d.Computes x o :=
  ⟨fun ⟨t, ht⟩ => ⟨_, t, Prod.ext rfl ht⟩, fun ⟨_, t, ht⟩ => ⟨t, by rw [ht]⟩⟩

variable {Symbol S : Type} [Fintype S] [Fintype Symbol] (eS : S ↪ ℕ) (eY : Symbol ↪ ℕ)

/-- The machine described by the description of `tm` halts on the renamed input exactly when `tm`
halts on the input. -/
theorem Desc.halts_desc (tm : MultiTapeTM k Symbol S) (x : List Symbol) :
    (desc eS eY tm).Halts (x.map eY) ↔ tm.Halts x := by
  simp only [Desc.Halts, MultiTapeTM.Halts, simulate_desc, Option.isNone_iff_eq_none,
    Cfg.Halted]

/-- The machine described by the description of `tm` halts on the renamed input with the renamed
output exactly when `tm` halts on the input with the output. -/
theorem Desc.computes_desc (tm : MultiTapeTM k Symbol S) (x out : List Symbol) :
    (desc eS eY tm).Computes (x.map eY) (out.map eY) ↔ tm.Computes x out := by
  simp only [Desc.Computes, MultiTapeTM.Computes, simulate_desc, Prod.mk.injEq,
    (List.map_injective_iff.mpr eY.injective).eq_iff, Option.isNone_iff_eq_none, Cfg.Halted]
  exact exists_congr fun _ => and_comm

end Universal

end Turing.MultiTapeTM
