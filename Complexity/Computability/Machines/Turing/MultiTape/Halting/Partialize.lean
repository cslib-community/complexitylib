/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Basic

/-!
# Machines that diverge on a verdict

A machine computing a total function can compute a partial one: let the first symbol it emits be a
verdict. `tm.partialize` runs `tm`, but reads the first emitted symbol as a verdict instead of
emitting it. After the verdict `true` it emits nothing, and once `tm` halts it loops forever in a
state of its own; after the verdict `false` it emits the rest of the output of `tm` and halts with
`tm`. So if `tm` halts with the output `encPartial r` on an input, encoding the divergence
`r = none` as `[true]` and an output `r = some o` as `false :: o`, then `tm.partialize` diverges
on that input when `r = none` and halts with output `o` when `r = some o`
(`Turing.MultiTapeTM.Computes.partialize`).

The proof is a step-by-step correspondence: the configurations of `tm.partialize` are images of the
configurations of `tm` under a map commuting with the steps
(`Turing.MultiTapeTM.Partialize.step_liftCfg`), so its runs are the images of the runs of `tm`
(`Turing.MultiTapeTM.runFrom_partialize`).

## Main definitions

* `Turing.MultiTapeTM.partialize`: the machine diverging on the verdict `true`.
* `Turing.MultiTapeTM.encPartial`: partial results as words.

## Main results

* `Turing.MultiTapeTM.runFrom_partialize`: the runs of `tm.partialize`.
* `Turing.MultiTapeTM.Computes.partialize`, `Turing.MultiTapeTM.Computes.halts_partialize`:
  `tm.partialize` computes the partial result encoded by the output of `tm`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 3.1][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace Partialize

/-- The verdict read from an output: its first symbol, if any. -/
def verdict (out : List Bool) : Option Bool := out.head?

/-- What follows the verdict `false` in an output; nothing before a verdict or after the verdict
`true`. -/
def strip : List Bool → List Bool
  | false :: out => out
  | _ => []

/-- The state of `tm.partialize` for a state of `tm` and a verdict: a running state is kept with
the verdict; once `tm` halts, the verdict `true` loops in the state `(none, some true)` and every
other verdict halts. -/
def liftState {State : Type*} : Option State → Option Bool → Option (Option State × Option Bool)
  | some q, v => some (some q, v)
  | none, v => if v = some true then some (none, some true) else none

/-- Emitting a symbol fixes the verdict if there was none. -/
theorem verdict_append (out : List Bool) (o : Option Bool) :
    verdict (out ++ o.toList) = (verdict out).or o := by
  cases out <;> cases o <;> rfl

/-- Emitting a symbol extends what follows the verdict only after the verdict `false`. -/
theorem strip_append (out : List Bool) (o : Option Bool) :
    strip (out ++ o.toList) =
      strip out ++ (if verdict out = some false then o else none).toList := by
  rcases out with _ | ⟨_ | _, out⟩
  · rcases o with _ | _ | _ <;> rfl
  · simp [strip, verdict]
  · simp [strip, verdict]

end Partialize

open Partialize

variable {k : ℕ} {State : Type*}

/-- `tm.partialize` runs `tm`, reading the first symbol it emits as a verdict. After the verdict
`true` it emits nothing, and once `tm` halts it loops forever in the state `(none, some true)`.
After the verdict `false` it emits the rest of the output of `tm` and halts with `tm`. The second
component of a state is the verdict read so far. -/
noncomputable def partialize (tm : MultiTapeTM k Bool State) :
    MultiTapeTM k Bool (Option State × Option Bool) :=
  ofTr (some tm.q₀, none) fun
    | (some q, v), inp, work =>
      { inputTape := (tm.tr q inp work).inputTape
        workTapes := (tm.tr q inp work).workTapes
        output := if v = some false then (tm.tr q inp work).output else none
        state := liftState (tm.tr q inp work).state (v.or (tm.tr q inp work).output) }
    | (none, v), _, _ =>
      { inputTape := 0
        workTapes := fun _ => (none, 0)
        output := none
        state := some (none, v) }

namespace Partialize

variable {input : List Bool}

/-- The configuration of `tm.partialize` corresponding to a configuration of `tm`: the state
carries the verdict of the output, and the output keeps what follows the verdict `false`. -/
def liftCfg (c : Cfg k Bool State input) : Cfg k Bool (Option State × Option Bool) input :=
  ⟨liftState c.state (verdict c.output), c.inputPos, c.workTapes, c.workTapePos, strip c.output⟩

/-- The symbol under the input head is that of `tm`. -/
theorem inputSymbol_liftCfg (c : Cfg k Bool State input) :
    (liftCfg c).inputSymbol = c.inputSymbol := rfl

/-- The symbols under the work-tape heads are those of `tm`. -/
theorem workTapeSymbols_liftCfg (c : Cfg k Bool State input) :
    (liftCfg c).workTapeSymbols = c.workTapeSymbols := rfl

/-- `tm.partialize` steps along `tm`. -/
theorem step_liftCfg (tm : MultiTapeTM k Bool State) (c : Cfg k Bool State input) :
    tm.partialize.step (liftCfg c) = liftCfg (tm.step c) := by
  obtain ⟨_ | q, ip, wt, wp, out⟩ := c
  · rw [step_of_halt (show Cfg.Halted ⟨none, ip, wt, wp, out⟩ from rfl)]
    by_cases hv : verdict out = some true
    · rw [step_of_state (q := (none, some true)) (by simp [liftCfg, liftState, hv])]
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
        simp [liftCfg, liftState, hv, partialize, Action.apply]
    · exact step_of_halt (by simp [liftCfg, liftState, hv])
  · rw [step_of_state (q := q) rfl, step_of_state (q := (some q, verdict out)) rfl,
      inputSymbol_liftCfg, workTapeSymbols_liftCfg]
    simp only [partialize, tr_ofTr]
    generalize tm.tr q _ _ = a
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [liftCfg, Action.apply, verdict_append, strip_append]

/-- `tm.partialize` has halted when `tm` has, unless the verdict is `true`. -/
theorem liftCfg_halted_iff (c : Cfg k Bool State input) :
    (liftCfg c).Halted ↔ c.Halted ∧ verdict c.output ≠ some true := by
  obtain ⟨_ | q, ip, wt, wp, out⟩ := c <;> by_cases hv : verdict out = some true <;>
    simp [liftCfg, liftState, hv, Cfg.Halted]

@[simp]
theorem output_liftCfg (c : Cfg k Bool State input) : (liftCfg c).output = strip c.output := rfl

end Partialize

/-- **The runs of `tm.partialize`** are the images of the runs of `tm`. -/
theorem runFrom_partialize (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    tm.partialize.runFrom (tm.partialize.initCfg input) t =
      liftCfg (tm.runFrom (tm.initCfg input) t) :=
  (Function.Semiconj.iterate_right (fun c => (step_liftCfg tm c).symm) t
    (tm.initCfg input)).symm

/-- Partial results as words: the divergence `none` as `[true]`, the output `some o` as
`false :: o`. -/
def encPartial : Option (List Bool) ↪ List Bool :=
  ⟨fun | none => [true] | some o => false :: o, by
    rintro (_ | o) (_ | o') h <;> simp_all⟩

@[simp] theorem encPartial_none : encPartial none = [true] := rfl

@[simp] theorem encPartial_some (o : List Bool) : encPartial (some o) = false :: o := rfl

variable {tm : MultiTapeTM k Bool State} {input : List Bool} {r : Option (List Bool)}

/-- **`tm.partialize` computes the partial result encoded by the output of `tm`**: if `tm` halts
with output `encPartial r`, then `tm.partialize` halts with output `o` exactly when `r = some o`,
and diverges when `r = none`. -/
theorem Computes.partialize (h : tm.Computes input (encPartial r)) (o : List Bool) :
    tm.partialize.Computes input o ↔ o ∈ r := by
  -- once `tm` has halted, its output is `encPartial r`
  have hout {t : ℕ} (ht : (tm.runFrom (tm.initCfg input) t).Halted) :=
    h.output_eq_of_halted ht
  have hhalt {t : ℕ} :
      (tm.partialize.runFrom (tm.partialize.initCfg input) t).Halted ↔
        (tm.runFrom (tm.initCfg input) t).Halted ∧ r.isSome := by
    rw [runFrom_partialize, liftCfg_halted_iff]
    refine and_congr_right fun ht => ?_
    rw [hout ht]
    cases r <;> simp [verdict]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨ht', hr⟩ := hhalt.mp ht
    obtain ⟨o, rfl⟩ := Option.isSome_iff_exists.mp hr
    rw [runFrom_partialize, output_liftCfg, hout ht']
    rfl
  · rintro rfl
    obtain ⟨u, hu, -⟩ := h
    refine ⟨u, hhalt.mpr ⟨hu, rfl⟩, ?_⟩
    rw [runFrom_partialize, output_liftCfg, hout hu]
    rfl

/-- If `tm` halts with output `encPartial r`, then `tm.partialize` halts exactly when `r` is a
result. -/
theorem Computes.halts_partialize (h : tm.Computes input (encPartial r)) :
    tm.partialize.Halts input ↔ r.isSome := by
  simp only [halts_iff_exists_computes, h.partialize, Option.mem_def, Option.isSome_iff_exists]

end Turing.MultiTapeTM
