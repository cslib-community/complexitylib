/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sampling
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic

/-!
# Sampling a certificate beside a framed word

`Turing.MultiTapePTM.pairSampler` is one fixed fair-coin machine with three control states and no
work tapes. On an input `frame y ++ r` it copies `frame y` to the output, then emits one fresh
fair bit for each symbol of `r`, and halts at the right boundary. So it outputs `frame y ++ w`,
the pair encoding of `(y, w)`, for a uniform word `w` of length `r.length`. It takes exactly
`(frame y ++ r).length + 1` transitions. Each copying transition also draws a coin, and ignores
it. Read nondeterministically, the machine guesses a certificate for the framed instance.

## Main definitions

* `Turing.MultiTapePTM.pairSampler`: the framed copier and certificate sampler.

## Main results

* `Turing.MultiTapePTM.eval_pairSampler`: the output is a uniform certificate after the framed
  word.
* `Turing.MultiTapePTM.pairSampler_halted`: every run has halted at the linear clock.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeTM

namespace PairSampler

/-- The control phases: before a frame tag, before a framed data bit, and in the sampled tail. -/
inductive Phase
  | tag
  | data
  | tail
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.tag, .data, .tail}, fun q => by cases q <;> simp⟩

/-- The control state after reading a symbol. The right boundary halts. -/
def next : Phase → Option Bool → Option Phase
  | _, none => none
  | .tag, some true => some .data
  | .tag, some false => some .tail
  | .data, some _ => some .tag
  | .tail, some _ => some .tail

/-- The emitted symbol. Framed symbols are copied, and tail symbols are replaced by the coin. -/
def emit : Phase → Option Bool → Bool → Option Bool
  | _, none, _ => none
  | .tail, some _, bit => some bit
  | .tag, some b, _ => some b
  | .data, some b, _ => some b

end PairSampler

open PairSampler in
/-- Copy a framed word, then emit one fair bit per remaining input symbol, and halt at the right
boundary, without work tapes. -/
def pairSampler : MultiTapePTM 0 Bool Phase where
  initial := .tag
  tr q symbol _ _ bit := .step
    { inputTape := if symbol.isSome then 1 else 0
      workTapes := Fin.elim0
      output := emit q symbol bit
      state := next q symbol }
    Empty.elim Empty.elim

namespace PairSampler

/-- The sampler at an input position, with the output written so far. -/
private def config (input : List Bool) (state : Option Phase) (index : ℕ) (output : List Bool)
    (h : index ≤ input.length) : Config 0 Bool Phase Empty input where
  tapes :=
    { state := state
      inputPos := ⟨index + 1, by lia⟩
      workTapes := Fin.elim0
      workTapePos := Fin.elim0
      output := output }

/-- Reading a remaining symbol writes the emitted symbol and advances once. -/
private theorem step {input output : List Bool} {index : ℕ} (h : index < input.length)
    (q : Phase) (o : Option Bool) (s : Option Phase) :
    (config input (some q) index output (by lia)).step
      { inputTape := 1, workTapes := Fin.elim0, output := o, state := s }
      Empty.elim Empty.elim =
      config input s (index + 1) (output ++ o.toList) h := by
  refine Config.ext ?_ (funext fun oracle => oracle.elim)
  refine Cfg.ext_zero_tapes rfl ?_ rfl
  apply Fin.ext
  change (moveInputPos _ .pos).val = index + 1 + 1
  rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
  rfl

/-- One live transition at a remaining symbol: draw a coin and take the selected step. -/
private theorem eval_run_succ {input output : List Bool} {index : ℕ} (h : index < input.length)
    (q : Phase) (fuel : ℕ) :
    ProbComp.eval (pairSampler.runClosedConfigFrom (fuel + 1)
      (config input (some q) index output (by lia))) =
      ProbComp.eval (ProbComp.uniform Bool >>= fun bit =>
        pairSampler.runClosedConfigFrom fuel
          (config input (next q (some input[index])) (index + 1)
            (output ++ (emit q (some input[index]) bit).toList) h)) := by
  have hsym := inputSymbolInner (cfg :=
    (config input (some q) index output (by lia)).tapes) index (by simp [config]; lia) h
  rw [runClosedConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
  simp only [show (config input (some q) index output (by lia)).tapes.state = some q from rfl,
    hsym, pairSampler, Option.isSome_some, ↓reduceIte, bind_map_left, step h]
  rfl

/-- At the right boundary the sampler halts, drawing and discarding one coin. -/
private theorem eval_run_boundary (input output : List Bool) (q : Phase) (fuel : ℕ) :
    ProbComp.eval (pairSampler.runClosedConfigFrom (fuel + 1)
      (config input (some q) input.length output le_rfl)) =
      PMF.pure (config input none input.length output le_rfl) := by
  have hsym := inputSymbol_eq_none_of_boundary (cfg :=
    (config input (some q) input.length output le_rfl).tapes)
    (Or.inr (by simp [config]))
  rw [runClosedConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
  simp only [show (config input (some q) input.length output le_rfl).tapes.state = some q from rfl,
    pairSampler, hsym, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, bind_map_left]
  have hcfg : ∀ bit : Bool, (config input (some q) input.length output le_rfl).step
      { inputTape := 0, workTapes := Fin.elim0, output := emit q none bit,
        state := next q none } Empty.elim Empty.elim =
      config input none input.length output le_rfl := by
    intro bit
    refine Config.ext ?_ (funext fun oracle => oracle.elim)
    refine Cfg.ext_zero_tapes ?_ (by simp [Config.step, config, Turing.Action.apply]) ?_
    · cases q <;> rfl
    · cases q <;> simp [Config.step, config, Turing.Action.apply, emit]
  simp only [hcfg]
  rcases fuel with _ | fuel
  · simp only [MultiTapeMachine.runConfigFrom, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_const]
  · have hhalt : ∀ n, ProbComp.eval (pairSampler.runClosedConfigFrom n
        (config input none input.length output le_rfl)) =
        PMF.pure (config input none input.length output le_rfl) := by
      intro n
      cases n with
      | zero => simp [runClosedConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
      | succ n =>
        rw [runClosedConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
        simp [config]
    simp only [ProbComp.eval_bind]
    change (ProbComp.eval (ProbComp.uniform Bool)).bind (fun _ => ProbComp.eval
      (pairSampler.runClosedConfigFrom (fuel + 1)
        (config input none input.length output le_rfl))) = _
    rw [hhalt, PMF.bind_const]

/-- The tail phase: one fresh fair bit per remaining symbol, then halting at the boundary. -/
private theorem eval_run_tail (input : List Bool) (remaining : ℕ) :
    ∀ (index : ℕ) (output : List Bool) (h : index + remaining = input.length),
      ProbComp.eval (pairSampler.runClosedConfigFrom (remaining + 1)
        (config input (some .tail) index output (by lia))) =
        (BitString.uniformList remaining).map
          (fun tail => config input none input.length (output ++ tail) le_rfl) := by
  induction remaining with
  | zero =>
    intro index output h
    have hi : index = input.length := by lia
    subst index
    rw [eval_run_boundary]
    simp [BitString.uniformList_zero, PMF.pure_map]
  | succ remaining ih =>
    intro index output h
    have hi : index < input.length := by lia
    rw [eval_run_succ hi]
    simp only [next, emit, Option.toList_some]
    simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ih (index + 1) _ (by lia),
      BitString.uniformList_succ, PMF.map_bind, PMF.map_comp, Function.comp_def,
      List.append_assoc, List.singleton_append]

/-- The copying phase: a framed word is copied verbatim, ignoring the coins drawn meanwhile. -/
private theorem eval_run_frame (input rest : List Bool) (fuel : ℕ) (y : List Bool) :
    ∀ (pre output : List Bool) (hin : input = pre ++ frame y ++ rest),
      ProbComp.eval (pairSampler.runClosedConfigFrom ((frame y).length + fuel)
        (config input (some .tag) pre.length output (by subst hin; simp))) =
      ProbComp.eval (pairSampler.runClosedConfigFrom fuel
        (config input (some .tail) (pre.length + (frame y).length) (output ++ frame y)
          (by subst hin; simp))) := by
  induction y with
  | nil =>
    intro pre output hin
    have hlt : pre.length < input.length := by subst hin; simp [frame]
    have hget : input[pre.length] = false := by subst hin; simp [frame]
    rw [show (frame []).length + fuel = fuel + 1 by simp [frame]; lia, eval_run_succ hlt]
    simp only [hget, next, emit, Option.toList_some, ProbComp.eval_bind]
    change (ProbComp.eval (ProbComp.uniform Bool)).bind (fun _ => _) = _
    rw [PMF.bind_const]
    rfl
  | cons b y ih =>
    intro pre output hin
    have hlt : pre.length < input.length := by subst hin; simp [frame]
    have hlt' : pre.length + 1 < input.length := by subst hin; simp [frame]
    have hget : input[pre.length] = true := by subst hin; simp [frame]
    have hget' : input[pre.length + 1] = b := by
      subst hin
      simp only [frame, List.flatMap_cons, List.append_assoc]
      rw [List.getElem_append_right (by simp)]
      simp
    have hlen : (frame (b :: y)).length + fuel = ((frame y).length + fuel + 1) + 1 := by
      simp [frame]; lia
    rw [hlen, eval_run_succ hlt]
    simp only [hget, next, emit, Option.toList_some, ProbComp.eval_bind]
    change (ProbComp.eval (ProbComp.uniform Bool)).bind (fun _ => _) = _
    rw [PMF.bind_const, eval_run_succ hlt']
    simp only [hget', next, emit, Option.toList_some, ProbComp.eval_bind]
    change (ProbComp.eval (ProbComp.uniform Bool)).bind (fun _ => _) = _
    rw [PMF.bind_const]
    have hpre : input = (pre ++ [true, b]) ++ frame y ++ rest := by
      subst hin; simp [frame]
    have := ih (pre ++ [true, b]) (output ++ [true] ++ [b]) hpre
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    convert this using 3
    · congr 1
      · simp [frame]; lia
      · simp

end PairSampler

open PairSampler

/-- The final configuration retains the framed word and a uniform certificate, and has halted at
the right boundary. -/
private theorem eval_runClosedConfig_pairSampler (y r : List Bool) :
    ProbComp.eval (pairSampler.runClosedConfigFrom ((frame y ++ r).length + 1)
      (pairSampler.initialConfig (frame y ++ r))) =
      (BitString.uniformList r.length).map (fun w =>
        PairSampler.config (frame y ++ r) none (frame y ++ r).length (frame y ++ w) le_rfl) := by
  have hcfg : pairSampler.initialConfig (frame y ++ r) =
      PairSampler.config (frame y ++ r) (some .tag) ([] : List Bool).length [] (by simp) := by
    refine Config.ext ?_ rfl
    exact Cfg.ext_zero_tapes rfl rfl rfl
  rw [hcfg, show (frame y ++ r).length + 1 = (frame y).length + (r.length + 1) by simp; lia,
    eval_run_frame (frame y ++ r) r (r.length + 1) y [] [] (by simp)]
  simpa only [List.length_nil, zero_add, List.nil_append] using
    eval_run_tail (frame y ++ r) r.length (frame y).length (frame y) (by simp)

/-- The sampler outputs a uniform certificate after the framed word, in a linear number of
transitions. -/
theorem eval_pairSampler (y r : List Bool) :
    ProbComp.eval (pairSampler.runClosed ((frame y ++ r).length + 1) (frame y ++ r)) =
      (BitString.uniformList r.length).map (frame y ++ ·) := by
  rw [runClosed_eq_map, ProbComp.eval_map, eval_runClosedConfig_pairSampler, PMF.map_comp]
  rfl

/-- Every supported configuration has actually halted by the linear clock. -/
theorem pairSampler_halted (y r : List Bool) :
    ∀ final ∈ (ProbComp.eval (pairSampler.runClosedConfigFrom ((frame y ++ r).length + 1)
      (pairSampler.initialConfig (frame y ++ r)))).support, final.tapes.state = none := by
  intro final hfinal
  rw [eval_runClosedConfig_pairSampler] at hfinal
  obtain ⟨output, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  rfl

end Turing.MultiTapePTM
