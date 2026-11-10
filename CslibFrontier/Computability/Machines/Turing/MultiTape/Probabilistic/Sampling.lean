/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
public import CslibFrontier.Languages.Probabilistic.BitString

/-!
# A uniform word sampler

One fixed machine with one control state and no work tapes scans its input, emitting a fresh fair
bit per symbol and halting at the right boundary. On an input of length `n` it writes a uniform
word of length `n` in exactly `n + 1` transitions. The last transition samples and discards a coin,
as the common interpreter does on every live instruction; the results below concern closed
distributions, not equality of programs with different numbers of coin queries.

## Main definitions

* `Turing.MultiTapePTM.uniformListMachine`: the finite uniform scanner.

## Main results

* `Turing.MultiTapePTM.eval_uniformListMachine`: uniform output at the linear clock.
* `Turing.MultiTapePTM.uniformListMachine_halted`: every run has halted at that clock.

## References

Adapted from Cslib/Computability/Probabilistic/Sampling.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine and input length.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

/-- Emit one fair bit per input symbol, then halt without using work tapes. -/
def uniformListMachine : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ symbol _ _ bit := .step
    { inputTape := if symbol.isSome then 1 else 0
      workTapes := Fin.elim0
      output := if symbol.isSome then some bit else none
      state := if symbol.isSome then some () else none }
    Empty.elim Empty.elim

namespace UniformListMachine

/-- The scanner at an input position, with the output written so far. -/
def config (input : List Bool) (state : Option Unit) (index : ℕ) (output : List Bool)
    (h : index ≤ input.length) : Config 0 Bool Unit Empty input where
  tapes :=
    { state := state
      inputPos := ⟨index + 1, by lia⟩
      workTapes := Fin.elim0
      workTapePos := Fin.elim0
      output := output }

/-- Reading any remaining symbol writes the sampled bit and advances once. -/
theorem step {input output : List Bool} {index : ℕ} (h : index < input.length) (bit : Bool) :
    (config input (some ()) index output (by lia)).step
      { inputTape := 1, workTapes := Fin.elim0, output := some bit, state := some () }
      Empty.elim Empty.elim =
      config input (some ()) (index + 1) (output ++ [bit]) h := by
  refine Config.ext ?_ (funext fun oracle => oracle.elim)
  refine Cfg.ext_zero_tapes rfl ?_ rfl
  apply Fin.ext
  change (moveInputPos _ .pos).val = index + 1 + 1
  rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
  rfl

/-- The complete configuration distribution after scanning the remaining suffix and halting. -/
theorem eval_run_config (input : List Bool) (remaining : ℕ) :
    ∀ (index : ℕ) (output : List Bool) (h : index + remaining = input.length),
      ProbComp.eval (uniformListMachine.runClosedConfigFrom (remaining + 1)
        (config input (some ()) index output (by lia))) =
        (BitString.uniformList remaining).map
          (fun tail => config input none input.length (output ++ tail) le_rfl) := by
  induction remaining with
  | zero =>
    intro index output h
    have hi : index = input.length := by lia
    subst index
    have hsym := inputSymbol_eq_none_of_boundary (cfg :=
      (config input (some ()) input.length output le_rfl).tapes)
      (Or.inr (by simp [config]))
    rw [runClosedConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
    simp only [
      show (config input (some ()) input.length output le_rfl).tapes.state = some () from rfl,
      uniformListMachine, hsym, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, bind_map_left]
    simp only [MultiTapeMachine.runConfigFrom, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_const, BitString.uniformList_zero, PMF.pure_map, List.append_nil]
    congr 1
    refine Config.ext ?_ (funext fun oracle => oracle.elim)
    exact Cfg.ext_zero_tapes rfl (by simp [Config.step, config, Turing.Action.apply])
      (by simp [Config.step, config, Turing.Action.apply])
  | succ remaining ih =>
    intro index output h
    have hi : index < input.length := by lia
    have hsym := inputSymbolInner (cfg :=
      (config input (some ()) index output (by lia)).tapes) index (by simp [config]; lia) hi
    rw [runClosedConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
    simp only [
      show (config input (some ()) index output (by lia)).tapes.state = some () from rfl,
      hsym, uniformListMachine, Option.isSome_some, ↓reduceIte, bind_map_left, step hi]
    change (ProbComp.eval (ProbComp.uniform Bool >>= fun bit =>
      uniformListMachine.runClosedConfigFrom (remaining + 1)
        (config input (some ()) (index + 1) (output ++ [bit]) hi))) = _
    simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ih (index + 1) _ (by lia),
      BitString.uniformList_succ, PMF.map_bind, PMF.map_comp, Function.comp_def,
      List.append_assoc, List.singleton_append]

end UniformListMachine

/-- The final configuration retains the generated word and has halted at the right boundary. -/
theorem eval_runClosedConfig_uniformListMachine (input : List Bool) :
    ProbComp.eval (uniformListMachine.runClosedConfigFrom (input.length + 1)
      (uniformListMachine.initialConfig input)) =
      (BitString.uniformList input.length).map
        (fun output => UniformListMachine.config input none input.length output le_rfl) := by
  have hcfg : uniformListMachine.initialConfig input =
      UniformListMachine.config input (some ()) 0 [] (Nat.zero_le _) := by
    refine Config.ext ?_ rfl
    exact Cfg.ext_zero_tapes rfl rfl rfl
  rw [hcfg]
  simpa only [List.nil_append] using
    UniformListMachine.eval_run_config input input.length 0 [] (by lia)

/-- The scanner outputs a uniform word of the input length in a linear number of transitions. -/
theorem eval_uniformListMachine (input : List Bool) :
    ProbComp.eval (uniformListMachine.runClosed (input.length + 1) input) =
      BitString.uniformList input.length := by
  rw [runClosed_eq_map, ProbComp.eval_map, eval_runClosedConfig_uniformListMachine,
    PMF.map_comp]
  exact PMF.map_id _

/-- Every supported configuration has actually halted by the linear clock. -/
theorem uniformListMachine_halted (input : List Bool) :
    ∀ final ∈ (ProbComp.eval (uniformListMachine.runClosedConfigFrom (input.length + 1)
      (uniformListMachine.initialConfig input))).support, final.tapes.state = none := by
  intro final hfinal
  rw [eval_runClosedConfig_uniformListMachine] at hfinal
  obtain ⟨output, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  rfl

end Turing.MultiTapePTM
