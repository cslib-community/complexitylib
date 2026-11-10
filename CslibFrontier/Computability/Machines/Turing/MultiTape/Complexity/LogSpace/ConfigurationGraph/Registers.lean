/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Correctness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Foundations.Relation.Transport

/-!
# Configuration graphs on register tuples

The compact configuration graph packs the registers of a view into one radix-`B` number. This
file states the same graph directly on register tuples, without packing: `RegisterStep` reads the
input symbol under the input head straight from the input word, matches the observations of a
permitted transition and applies `nextRegisters`. Halted tuples step only to themselves.

Register-tuple reachability from `startRegisters` is exactly the set of registers of reachable
views (`reflTransGen_registerStep_iff`), so acceptance is reachability of a halted tuple with
output tag `1` (`accepts_iff_registerStep`). When every reachable view fits a radix `B`, the same
holds on tuples of type `Register k → Fin B` (`accepts_iff_registerStep_fin`). These are the forms
used by logical descriptions of configuration graphs, in which a configuration is a fixed tuple
of universe elements.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.startRegisters`: the initial register tuple.
* `Turing.MultiTapeNTM.ConfigurationGraph.RegisterStep`: one step on register tuples.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.reflTransGen_registerStep_iff`: reachable tuples are the
  registers of reachable views.
* `Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_registerStep`: acceptance on ℕ-valued tuples.
* `Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_registerStep_fin`: acceptance on bounded
  tuples.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

public section

open Cslib.Turing

namespace Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]

/-- The registers of the initial view: input head on the first cell, the initial control and
blank work tapes. -/
@[expose] noncomputable def startRegisters (ntm : MultiTapeNTM k Bool State) : Register k → ℕ
  | .inputPos => 1
  | .control => stateCode (some ntm.q₀)
  | _ => 0

/-- One step on register tuples over the input `w`. A tuple whose control is the halting tag
steps to itself. Otherwise some permitted transition observes the control, the input symbol
under the input head and the work-tape head symbols, and the successor is `nextRegisters`. -/
@[expose] def RegisterStep (ntm : MultiTapeNTM k Bool State) (w : List Bool)
    (r r' : Register k → ℕ) : Prop :=
  (r .control = stateCode (none : Option State) ∧ r' = r) ∨
    ∃ (q : State) (s : Option Bool) (heads : Fin k → Option Bool) (a : Action k Bool State),
      ntm.Tr q s heads a ∧ r .control = stateCode (some q) ∧ inputAt w (r .inputPos) = s ∧
        (∀ i, r (.head i) = symbolCode (heads i)) ∧ r' = nextRegisters w.length r a

variable {ntm : MultiTapeNTM k Bool State} {w : List Bool}

/-- The initial view has the start registers. -/
theorem registers_initView (w : List Bool) :
    registers (ntm.initView w) = startRegisters ntm := by
  funext i
  cases i <;> rfl

/-- Every view step is a register step on the view's input. -/
theorem registerStep_of_viewStep {v v' : FiniteCfg k Bool State} (h : ntm.ViewStep v v') :
    RegisterStep ntm v.input (registers v) (registers v') := by
  cases hs : v.state with
  | none =>
    have hv : v' = v := by simpa [ViewStep, hs] using h
    subst hv
    exact .inl ⟨by simp [registers, hs], rfl⟩
  | some q =>
    obtain ⟨a, ha, rfl⟩ : ∃ a, ntm.Tr q v.inputSymbol v.workTapeSymbols a ∧
        v' = (v.step a).summarizeOutput := by simpa [ViewStep, hs] using h
    refine .inr ⟨q, v.inputSymbol, v.workTapeSymbols, a, ha, by simp [registers, hs], ?_,
      fun _ => rfl, registers_step v a⟩
    exact (Cfg.inputSymbol_eq_inputAt v.toCfg).symm

/-- Every register step out of the registers of a view is the registers of a view step. -/
theorem exists_viewStep_of_registerStep {v : FiniteCfg k Bool State} {r : Register k → ℕ}
    (h : RegisterStep ntm v.input (registers v) r) :
    ∃ v', ntm.ViewStep v v' ∧ v'.input = v.input ∧ registers v' = r := by
  rcases h with ⟨hc, rfl⟩ | ⟨q, s, heads, a, ha, hc, hin, hh, rfl⟩
  · have hs : v.state = none := stateCode_injective hc
    exact ⟨v, by simp [ViewStep, hs], rfl, rfl⟩
  · have hs : v.state = some q := stateCode_injective hc
    have hin' : v.inputSymbol = s := (Cfg.inputSymbol_eq_inputAt v.toCfg).trans hin
    have hw : v.workTapeSymbols = heads := funext fun i => symbolCode_injective (hh i)
    refine ⟨(v.step a).summarizeOutput, ?_, rfl, registers_step v a⟩
    simp only [ViewStep, hs]
    exact ⟨a, by rwa [hin', hw], rfl⟩

/-- **Reachable register tuples are the registers of reachable views.** -/
theorem reflTransGen_registerStep_iff (r : Register k → ℕ) :
    Relation.ReflTransGen (RegisterStep ntm w) (startRegisters ntm) r ↔
      ∃ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v ∧ registers v = r := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨_, .refl, registers_initView w⟩
    | @tail a b _ hab ih =>
      obtain ⟨v, hv, rfl⟩ := ih
      rw [← input_of_reachable hv] at hab
      obtain ⟨v', hstep, _, rfl⟩ := exists_viewStep_of_registerStep hab
      exact ⟨v', hv.tail hstep, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    induction hv with
    | refl => rw [registers_initView]
    | @tail a b hab hstep ih =>
      have hstep' := registerStep_of_viewStep hstep
      rw [input_of_reachable hab] at hstep'
      exact ih.tail hstep'

/-- **Acceptance is register-tuple reachability**: a machine accepts exactly when a tuple with the
halting control tag and output tag `1` is reachable from the start registers. -/
theorem accepts_iff_registerStep :
    ntm.Accepts w ↔ ∃ r, Relation.ReflTransGen (RegisterStep ntm w) (startRegisters ntm) r ∧
      r .control = stateCode (none : Option State) ∧ r .output = 1 := by
  rw [accepts_iff_reflTransGen_viewStep]
  constructor
  · rintro ⟨v, hv, hs, ho⟩
    exact ⟨registers v, (reflTransGen_registerStep_iff _).mpr ⟨v, hv, rfl⟩,
      congrArg stateCode hs, outputCode_eq_one_iff.mpr ho⟩
  · rintro ⟨r, hr, hc, ho⟩
    obtain ⟨v, hv, rfl⟩ := (reflTransGen_registerStep_iff r).mp hr
    exact ⟨v, hv, stateCode_injective hc, outputCode_eq_one_iff.mp ho⟩

/-- **Acceptance on bounded register tuples**: when every reachable view fits the radix `B`,
acceptance is reachability between tuples of elements of `Fin B`, from a tuple holding the start
registers to one with the halting control tag and output tag `1`. -/
theorem accepts_iff_registerStep_fin {B : ℕ}
    (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits B (registers v)) :
    ntm.Accepts w ↔ ∃ x y : Register k → Fin B, (∀ i, (x i).val = startRegisters ntm i) ∧
      Relation.ReflTransGen (fun x y : Register k → Fin B =>
        RegisterStep ntm w (fun i => (x i).val) (fun i => (y i).val)) x y ∧
      (y .control).val = stateCode (none : Option State) ∧ (y .output).val = 1 := by
  let f : (Register k → Fin B) → Register k → ℕ := fun x i => (x i).val
  have hf : Function.Injective f := fun x y h => funext fun i => Fin.ext (congrFun h i)
  have hstart : Fits B (startRegisters ntm) := by
    rw [← registers_initView w]
    exact hfit _ .refl
  have hrange : ∀ r, Relation.ReflTransGen (RegisterStep ntm w) (startRegisters ntm) r →
      ∃ x, f x = r := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := (reflTransGen_registerStep_iff r).mp hr
    exact ⟨fun i => ⟨registers v i, hfit v hv i⟩, rfl⟩
  rw [accepts_iff_registerStep]
  constructor
  · rintro ⟨r, hr, hc, ho⟩
    let x : Register k → Fin B := fun i => ⟨startRegisters ntm i, hstart i⟩
    obtain ⟨y, rfl⟩ := hrange r hr
    exact ⟨x, y, fun _ => rfl,
      (Relation.reflTransGen_onFun_iff hf (a := x) (b := y) hrange).mpr hr, hc, ho⟩
  · rintro ⟨x, y, hx, hxy, hc, ho⟩
    have hfx : f x = startRegisters ntm := funext hx
    refine ⟨f y, ?_, hc, ho⟩
    rw [← hfx]
    exact Relation.ReflTransGen.lift f (fun _ _ h => h) _ _ hxy

end Turing.MultiTapeNTM.ConfigurationGraph
