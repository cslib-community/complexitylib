/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle

/-!
# Input-tape prefix locality of bounded machine runs

In `fuel` instructions from the initial configuration (`inputPos = 1`), the input head moves by at
most one cell per instruction, so it never reads an input index at or beyond `fuel` and never clamps
at the right boundary `input.length + 1` when at least `fuel` symbols are present. Consequently, a
`fuel`-step run of a `MultiTapeMachine` on `input` produces the exact same `OracleComp` output
program as on `input.take m` for any `m ≥ fuel`, and in particular a `fuel`-step run on `u ++ v`
depends only on `u ++ v.take fuel`.

Because this equality holds at the level of the uninterpreted `OracleComp` program, it applies to
every choice and query handler, including closed fair-coin runs (`MultiTapePTM.runClosed`) and
stateful external-oracle runs (`MultiTapePTM.runOracle`).

## Main results

* `Turing.MultiTapeMachine.runFrom_eq_of_prefix_agree`: agreement on an `m`-symbol input prefix
  preserves `runFrom` whenever `inputPos.val + fuel ≤ m + 1`.
* `Turing.MultiTapeMachine.run_take_of_le`, `Turing.MultiTapeMachine.run_take`: a `fuel`-step run
  from `initialConfig` depends only on `input.take fuel`.
* `Turing.MultiTapeMachine.run_append_take_of_le`, `Turing.MultiTapeMachine.run_append_take`: a
  `fuel`-step run on `u ++ v` depends only on `u ++ v.take fuel`.
* `Turing.MultiTapePTM.runClosed_take_of_le`, `Turing.MultiTapePTM.runClosed_take`,
  `Turing.MultiTapePTM.runClosed_append_take_of_le`, `Turing.MultiTapePTM.runClosed_append_take`:
  specializations to closed fair-coin runs.
* `Turing.MultiTapePTM.runOracle_take_of_le`, `Turing.MultiTapePTM.runOracle_take`,
  `Turing.MultiTapePTM.runOracle_append_take_of_le`, `Turing.MultiTapePTM.runOracle_append_take`:
  specializations to oracle fair-coin runs.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query} [DecidableEq Oracle]
  (machine : MultiTapeMachine k Symbol State Oracle Choose)
  (choose : Choose (Action k Symbol State Oracle) → OracleComp spec (Action k Symbol State Oracle))
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))

/-- Two configurations whose input words agree on the first `m` symbols (`m ≤ input₁.length`,
`m ≤ input₂.length`) and whose input head starts at a position `pos` with `pos + fuel ≤ m + 1`
produce the exact same output program over `fuel` steps: the input head never visits or clamps at
a cell beyond index `m - 1`. -/
theorem runFrom_eq_of_prefix_agree {input₁ input₂ : List Symbol} {m : ℕ}
    (hm₁ : m ≤ input₁.length) (hm₂ : m ≤ input₂.length)
    (hagree : ∀ j < m, input₁[j]? = input₂[j]?) (fuel : ℕ)
    (cfg₁ : Config k Symbol State Oracle input₁)
    (cfg₂ : Config k Symbol State Oracle input₂)
    (hstate : cfg₁.tapes.state = cfg₂.tapes.state)
    (hpos : cfg₁.tapes.inputPos.val = cfg₂.tapes.inputPos.val)
    (hwork : cfg₁.tapes.workTapes = cfg₂.tapes.workTapes)
    (hworkPos : cfg₁.tapes.workTapePos = cfg₂.tapes.workTapePos)
    (hout : cfg₁.tapes.output = cfg₂.tapes.output)
    (hchan : cfg₁.channels = cfg₂.channels)
    (hbound : cfg₁.tapes.inputPos.val + fuel ≤ m + 1) :
    machine.runFrom choose query fuel cfg₁ = machine.runFrom choose query fuel cfg₂ := by
  induction fuel generalizing cfg₁ cfg₂ with
  | zero => simp [hout]
  | succ fuel ih =>
    cases hs₁ : cfg₁.tapes.state with
    | none =>
      have hs₂ : cfg₂.tapes.state = none := hstate ▸ hs₁
      simp [runFrom, runConfigFrom, hs₁, hs₂, hout]
    | some state =>
      have hs₂ : cfg₂.tapes.state = some state := hstate ▸ hs₁
      have hsym : cfg₁.tapes.inputSymbol = cfg₂.tapes.inputSymbol := by
        by_cases h0 : cfg₁.tapes.inputPos.val = 0
        · rw [inputSymbol_eq_none_of_boundary (Or.inl h0),
            inputSymbol_eq_none_of_boundary (Or.inl (hpos ▸ h0))]
        · have hp₁ : cfg₁.tapes.inputPos.val - 1 < input₁.length := by lia
          have hp₂ : cfg₁.tapes.inputPos.val - 1 < input₂.length := by lia
          rw [inputSymbolInner (cfg₁.tapes.inputPos.val - 1) (by lia) hp₁,
            inputSymbolInner (cfg₁.tapes.inputPos.val - 1) (by lia) hp₂]
          have hj := hagree (cfg₁.tapes.inputPos.val - 1) (by lia)
          rwa [List.getElem?_eq_getElem hp₁, List.getElem?_eq_getElem hp₂] at hj
      have hworkSym : cfg₁.tapes.workTapeSymbols = cfg₂.tapes.workTapeSymbols := by
        funext i
        simp [Cfg.workTapeSymbols, hwork, hworkPos]
      have hansSym : cfg₁.answerSymbols = cfg₂.answerSymbols := by
        funext op
        simp [Config.answerSymbols, hchan]
      simp only [runFrom, runConfigFrom, hs₁, hs₂, hsym, hworkSym, hansSym, map_bind]
      congr 1
      funext action
      cases action with
      | step action symbol move =>
        have hmove₁ := val_moveInputPos_eq cfg₁.tapes.inputPos action.inputTape
        have hmove₂ := val_moveInputPos_eq cfg₂.tapes.inputPos action.inputTape
        have hcast : (action.inputTape.cast : ℤ) = -1 ∨ (action.inputTape.cast : ℤ) = 0 ∨
            (action.inputTape.cast : ℤ) = 1 := by
          rcases action.inputTape with _ | _ | _ <;> simp [SignType.cast]
        refine ih (cfg₁.step action symbol move) (cfg₂.step action symbol move)
          rfl ?_ ?_ ?_ ?_ ?_ ?_
        · simp only [Config.step, Turing.Action.apply_inputPos]
          lia
        · funext i
          simp [Config.step, Turing.Action.apply_workTapes, hwork, hworkPos]
        · funext i
          simp [Config.step, Turing.Action.apply_workTapePos, hworkPos]
        · simp [Config.step, Turing.Action.apply_output, hout]
        · funext op
          simp [Config.step, hchan]
        · simp only [Config.step, Turing.Action.apply_inputPos]
          lia
      | query op next =>
        have hq : (cfg₁.channels op).queryBuffer = (cfg₂.channels op).queryBuffer := by
          rw [hchan]
        simp only [hq, map_bind]
        congr 1
        funext answer
        refine ih (cfg₁.receive op next answer) (cfg₂.receive op next answer)
          rfl hpos hwork hworkPos hout ?_ (by simp [Config.receive]; lia)
        funext other
        simp [Config.receive, hchan]

/-- A `fuel`-step run from the initial configuration depends only on the first `m` input symbols
whenever `fuel ≤ m`: starting at `inputPos = 1`, the input head reads only indices below `fuel`. -/
theorem run_take_of_le {fuel m : ℕ} (hm : fuel ≤ m) (input : List Symbol) :
    machine.run choose query fuel (input.take m) = machine.run choose query fuel input := by
  rcases le_or_gt input.length m with hlen | hlen
  · rw [List.take_of_length_le hlen]
  · exact machine.runFrom_eq_of_prefix_agree choose query
      (by simp [List.length_take_of_le hlen.le]) hlen.le
      (fun j hj => List.getElem?_take_of_lt hj) fuel
      (machine.initialConfig (input.take m)) (machine.initialConfig input)
      rfl rfl rfl rfl rfl rfl (by simp [initialConfig]; lia)

/-- A `fuel`-step run from the initial configuration depends only on `input.take fuel`. -/
theorem run_take (fuel : ℕ) (input : List Symbol) :
    machine.run choose query fuel (input.take fuel) = machine.run choose query fuel input :=
  machine.run_take_of_le choose query le_rfl input

/-- A `fuel`-step run on `u ++ v` depends only on `u ++ v.take m` whenever `fuel ≤ m`. -/
theorem run_append_take_of_le {fuel m : ℕ} (hm : fuel ≤ m) (u v : List Symbol) :
    machine.run choose query fuel (u ++ v.take m) = machine.run choose query fuel (u ++ v) := by
  have htake : (u ++ v).take (u.length + m) = u ++ v.take m := by
    rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  rw [← htake, machine.run_take_of_le choose query (by lia)]

/-- **Prefix locality on `u ++ v`.** A `fuel`-step run on `u ++ v` depends only on
`u ++ v.take fuel`. -/
theorem run_append_take (fuel : ℕ) (u v : List Symbol) :
    machine.run choose query fuel (u ++ v.take fuel) = machine.run choose query fuel (u ++ v) :=
  machine.run_append_take_of_le choose query le_rfl u v

end Turing.MultiTapeMachine

namespace Turing.MultiTapePTM

variable {k : ℕ} {Symbol State Operation : Type} [DecidableEq Operation]

/-- A `fuel`-step closed run depends only on the first `m` input symbols whenever `fuel ≤ m`. -/
theorem runClosed_take_of_le (machine : MultiTapePTM k Symbol State) {fuel m : ℕ} (hm : fuel ≤ m)
    (input : List Symbol) :
    machine.runClosed fuel (input.take m) = machine.runClosed fuel input :=
  MultiTapeMachine.run_take_of_le machine _ _ hm input

/-- A `fuel`-step closed run depends only on `input.take fuel`. -/
theorem runClosed_take (machine : MultiTapePTM k Symbol State) (fuel : ℕ) (input : List Symbol) :
    machine.runClosed fuel (input.take fuel) = machine.runClosed fuel input :=
  machine.runClosed_take_of_le le_rfl input

/-- A `fuel`-step closed run on `u ++ v` depends only on `u ++ v.take m` whenever `fuel ≤ m`. -/
theorem runClosed_append_take_of_le (machine : MultiTapePTM k Symbol State) {fuel m : ℕ}
    (hm : fuel ≤ m) (u v : List Symbol) :
    machine.runClosed fuel (u ++ v.take m) = machine.runClosed fuel (u ++ v) :=
  MultiTapeMachine.run_append_take_of_le machine _ _ hm u v

/-- **Prefix locality for closed probabilistic runs.** A `fuel`-step closed run on `u ++ v`
depends only on `u ++ v.take fuel`. -/
theorem runClosed_append_take (machine : MultiTapePTM k Symbol State) (fuel : ℕ)
    (u v : List Symbol) :
    machine.runClosed fuel (u ++ v.take fuel) = machine.runClosed fuel (u ++ v) :=
  machine.runClosed_append_take_of_le le_rfl u v

/-- A `fuel`-step oracle run depends only on the first `m` input symbols whenever `fuel ≤ m`. -/
theorem runOracle_take_of_le (machine : MultiTapePTM k Symbol State Operation) {fuel m : ℕ}
    (hm : fuel ≤ m) (input : List Symbol) :
    machine.runOracle fuel (input.take m) = machine.runOracle fuel input :=
  MultiTapeMachine.run_take_of_le machine _ _ hm input

/-- A `fuel`-step oracle run depends only on `input.take fuel`. -/
theorem runOracle_take (machine : MultiTapePTM k Symbol State Operation) (fuel : ℕ)
    (input : List Symbol) :
    machine.runOracle fuel (input.take fuel) = machine.runOracle fuel input :=
  machine.runOracle_take_of_le le_rfl input

/-- A `fuel`-step oracle run on `u ++ v` depends only on `u ++ v.take m` whenever `fuel ≤ m`. -/
theorem runOracle_append_take_of_le (machine : MultiTapePTM k Symbol State Operation) {fuel m : ℕ}
    (hm : fuel ≤ m) (u v : List Symbol) :
    machine.runOracle fuel (u ++ v.take m) = machine.runOracle fuel (u ++ v) :=
  MultiTapeMachine.run_append_take_of_le machine _ _ hm u v

/-- **Prefix locality for oracle probabilistic runs.** A `fuel`-step oracle run on `u ++ v`
depends only on `u ++ v.take fuel`. -/
theorem runOracle_append_take (machine : MultiTapePTM k Symbol State Operation) (fuel : ℕ)
    (u v : List Symbol) :
    machine.runOracle fuel (u ++ v.take fuel) = machine.runOracle fuel (u ++ v) :=
  machine.runOracle_append_take_of_le le_rfl u v

end Turing.MultiTapePTM
