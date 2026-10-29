/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Closed

import Complexity.Probability.PMF.Bind

/-!
# Running a second fair-coin machine when the first does not accept

`first.orElse second` runs `first` on its own block of work tapes, with its output suppressed and
summarized in the control state by `Turing.MultiTapeNTM.outputClass`. If `first` halts with
output `[true]`, the machine outputs `true` and halts. Otherwise it moves the input head back to
the first input symbol and runs `second` on a separate, blank block of work tapes, with fresh coins.
One more work tape holds a flag recording that `first` accepted; the two phases are joined by
`Turing.MultiTapePTM.seq`. Both machines use the Boolean alphabet and no oracle channels.

If `first` and `second` halt on every branch within `t₁` and `t₂` steps on an input of length `n`,
then `first.orElse second` halts on every branch within `t₁ + (n + 2 + t₂)` steps: rewinding the
input head takes at most `n + 2` steps. Its output distribution is that of the program "run
`first`; if it outputs `[true]`, output `[true]`, and otherwise run `second`". Since both phases
halt, this is exact, not a bound. Every work-tape head stays within the cells that `first` or
`second` alone would use, so a space bound for both machines gives one for the combination.

The phases are analysed through two general rules for fair-coin machines without oracle
channels: a map of configurations commuting with each coin's step maps the configuration
distribution, and a step that ignores its coin is taken with certainty.

## Main definitions

* `Turing.MultiTapePTM.orElse`: run `second` if `first` does not accept.

## Main results

* `Turing.MultiTapePTM.runClosedConfigFromCoins_map`,
  `Turing.MultiTapePTM.eval_runClosedConfigFrom_map`: one-step simulation of coin replays and of
  configuration distributions.
* `Turing.MultiTapePTM.eval_runClosedConfigFrom_succ_of_step`: a step that does not depend on the
  coin is taken with certainty.
* `Turing.MultiTapePTM.step_withCoin_seq_left`, `Turing.MultiTapePTM.step_withCoin_seq_right`:
  steps of a sequential machine under a fixed coin.
* `Turing.MultiTapePTM.orElse_halted`: the combined halting time.
* `Turing.MultiTapePTM.eval_runClosed_orElse`: the output distribution.
* `Turing.MultiTapePTM.runsInSpace_toNTM_orElse`: the space bound of the nondeterministic view.

## References

Repeating a one-sided-error algorithm and accepting when some run accepts is the standard error
reduction for one-sided error [Arora and Barak, Section 7.4.1][AroraBarak09]; see
`Cslib.Complexity.mem_RL_iff_error_le` for its use in randomized logarithmic space.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

section Simulation

variable {k k' : ℕ} {Symbol S S' : Type} {input : List Symbol}

/-- A map of configurations that commutes with each coin's step commutes with every replay. -/
theorem runClosedConfigFromCoins_map (M : MultiTapePTM k Symbol S)
    (N : MultiTapePTM k' Symbol S')
    (f : Config k Symbol S Empty input → Config k' Symbol S' Empty input)
    (h : ∀ bit c, (N.withCoin bit).step (f c) = f ((M.withCoin bit).step c))
    (coins : List Bool) (c : Config k Symbol S Empty input) :
    N.runClosedConfigFromCoins coins (f c) = f (M.runClosedConfigFromCoins coins c) := by
  induction coins generalizing c with
  | nil => rfl
  | cons bit coins ih =>
    change N.runClosedConfigFromCoins coins ((N.withCoin bit).step (f c)) =
      f (M.runClosedConfigFromCoins coins ((M.withCoin bit).step c))
    rw [h, ih]

/-- **One-step simulation.** A map of configurations that commutes with each coin's step maps the
closed configuration distribution. -/
theorem eval_runClosedConfigFrom_map (M : MultiTapePTM k Symbol S)
    (N : MultiTapePTM k' Symbol S')
    (f : Config k Symbol S Empty input → Config k' Symbol S' Empty input)
    (h : ∀ bit c, (N.withCoin bit).step (f c) = f ((M.withCoin bit).step c))
    (fuel : ℕ) (c : Config k Symbol S Empty input) :
    ProbComp.eval (N.runClosedConfigFrom fuel (f c)) =
      (ProbComp.eval (M.runClosedConfigFrom fuel c)).map f := by
  rw [eval_runClosedConfigFrom_eq_map_coins, eval_runClosedConfigFrom_eq_map_coins, PMF.map_comp]
  congr 1
  funext coins
  exact runClosedConfigFromCoins_map M N f h coins c

/-- A step that does not depend on the coin is taken with certainty. -/
theorem eval_runClosedConfigFrom_succ_of_step (N : MultiTapePTM k' Symbol S')
    {c c' : Config k' Symbol S' Empty input} (h : ∀ bit, (N.withCoin bit).step c = c')
    (fuel : ℕ) :
    ProbComp.eval (N.runClosedConfigFrom (fuel + 1) c) =
      ProbComp.eval (N.runClosedConfigFrom fuel c') := by
  rw [eval_runClosedConfigFrom_eq_map_coins, eval_runClosedConfigFrom_eq_map_coins,
    BitString.uniformList_succ, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hcons (bit : Bool) (coins : List Bool) :
      N.runClosedConfigFromCoins (bit :: coins) c = N.runClosedConfigFromCoins coins c' := by
    change N.runClosedConfigFromCoins coins ((N.withCoin bit).step c) = _
    rw [h]
  simp only [hcons, PMF.bind_const]

/-- With a fixed coin, a running first phase of a sequential machine steps as the first machine. -/
theorem step_withCoin_seq_left {S₀ S₁ : Type} (first : MultiTapePTM k Symbol S₀)
    (second : MultiTapePTM k Symbol S₁) (bit : Bool) (c : Config k Symbol S₀ Empty input)
    (hc : c.tapes.state ≠ none) :
    ((first.seq second).withCoin bit).step (Sequential.left second c) =
      Sequential.left second ((first.withCoin bit).step c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  rw [Config.eq_iff_tapes_eq]
  have hstate : (Sequential.left second c).tapes.state = some (.inl q) := by
    simp [Sequential.left, Cfg.mapState, hq]
  have hinput : (Sequential.left second c).tapes.inputSymbol = c.tapes.inputSymbol := rfl
  have hwork : (Sequential.left second c).tapes.workTapeSymbols = c.tapes.workTapeSymbols := rfl
  have hans : (Sequential.left second c).answerSymbols = c.answerSymbols := Subsingleton.elim _ _
  have hmap (f : ReaderT Bool Id (MultiTapeMachine.Action k Symbol S₀ Empty)) :
      (Sequential.leftAction second.initial <$> f) bit =
        Sequential.leftAction second.initial (f bit) := rfl
  simp only [MultiTapeMachine.step, hstate, hq, withCoin, seq, MultiTapeMachine.seq, hinput,
    hwork, hans, hmap]
  cases first.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
  | step a s m =>
    simp [Sequential.leftAction, Sequential.left, Config.step, Turing.Action.apply, Cfg.mapState]
  | query op _ => exact op.elim

/-- With a fixed coin, the second phase of a sequential machine steps as the second machine. -/
theorem step_withCoin_seq_right {S₀ S₁ : Type} (first : MultiTapePTM k Symbol S₀)
    (second : MultiTapePTM k Symbol S₁) (bit : Bool) (c : Config k Symbol S₁ Empty input) :
    ((first.seq second).withCoin bit).step (Sequential.right (State₀ := S₀) c) =
      Sequential.right ((second.withCoin bit).step c) := by
  rw [Config.eq_iff_tapes_eq]
  cases hq : c.tapes.state with
  | none => simp [MultiTapeMachine.step, Sequential.right, Cfg.mapState, hq]
  | some q =>
    have hstate : (Sequential.right (State₀ := S₀) c).tapes.state = some (.inr q) := by
      simp [Sequential.right, Cfg.mapState, hq]
    have hinput : (Sequential.right (State₀ := S₀) c).tapes.inputSymbol =
        c.tapes.inputSymbol := rfl
    have hwork : (Sequential.right (State₀ := S₀) c).tapes.workTapeSymbols =
        c.tapes.workTapeSymbols := rfl
    have hans : (Sequential.right (State₀ := S₀) c).answerSymbols = c.answerSymbols :=
      Subsingleton.elim _ _
    have hmap (f : ReaderT Bool Id (MultiTapeMachine.Action k Symbol S₁ Empty)) :
        (Sequential.rightAction (State₀ := S₀) <$> f) bit = Sequential.rightAction (f bit) := rfl
    simp only [MultiTapeMachine.step, hstate, hq, withCoin, seq, MultiTapeMachine.seq, hinput,
      hwork, hans, hmap]
    cases second.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
    | step a s m =>
      simp [Sequential.rightAction, Sequential.right, Config.step, Turing.Action.apply,
        Cfg.mapState]
    | query op _ => exact op.elim

end Simulation

namespace OrElse

variable {k₁ k₂ : ℕ}

/-! ### Tape layout -/

/-- The work tapes of the combined machine: those of the first machine, those of the second
machine, and one flag tape recording that the first machine accepted. -/
private def layout {α : Type*} (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α) (f : α) :
    Fin (k₁ + k₂ + 1) → α :=
  Fin.append (Fin.append w₁ w₂) fun _ => f

/-- The tape of the combined machine holding tape `i` of the first machine. -/
private def tape₁ (k₂ : ℕ) (i : Fin k₁) : Fin (k₁ + k₂ + 1) := Fin.castAdd 1 (Fin.castAdd k₂ i)

/-- The tape of the combined machine holding tape `j` of the second machine. -/
private def tape₂ (k₁ : ℕ) (j : Fin k₂) : Fin (k₁ + k₂ + 1) := Fin.castAdd 1 (Fin.natAdd k₁ j)

/-- The flag tape. -/
private def flagTape (k₁ k₂ : ℕ) : Fin (k₁ + k₂ + 1) := Fin.natAdd (k₁ + k₂) 0

variable {α : Type*} {w₁ : Fin k₁ → α} {w₂ : Fin k₂ → α} {f : α}

@[simp] private theorem layout_tape₁ (i : Fin k₁) : layout w₁ w₂ f (tape₁ k₂ i) = w₁ i := by
  simp [layout, tape₁]

@[simp] private theorem layout_tape₂ (j : Fin k₂) : layout w₁ w₂ f (tape₂ k₁ j) = w₂ j := by
  simp [layout, tape₂]

@[simp] private theorem layout_flagTape : layout w₁ w₂ f (flagTape k₁ k₂) = f := by
  simp [layout, flagTape]

private theorem funext_layout {g h : Fin (k₁ + k₂ + 1) → α}
    (h₁ : ∀ i, g (tape₁ k₂ i) = h (tape₁ k₂ i))
    (h₂ : ∀ j, g (tape₂ k₁ j) = h (tape₂ k₁ j)) (hf : g (flagTape k₁ k₂) = h (flagTape k₁ k₂)) :
    g = h := by
  funext i
  refine Fin.addCases (fun i => Fin.addCases (fun i => h₁ i) (fun j => h₂ j) i) (fun i => ?_) i
  rwa [Fin.fin_one_eq_zero i]

/-! ### Output classes -/

/-- The class of an output word: `none` for the empty word, `some true` for `[true]`, and
`some false` for every other word. -/
private def outClass (word : List Bool) : Option Bool := (MultiTapeNTM.outputClass word).head?

@[simp] private theorem outClass_nil : outClass [] = none := rfl

private theorem toList_outClass (word : List Bool) :
    (outClass word).toList = MultiTapeNTM.outputClass word := by
  unfold outClass MultiTapeNTM.outputClass
  split_ifs <;> rfl

private theorem outClass_append (word : List Bool) (symbol : Option Bool) :
    outClass ((outClass word).toList ++ symbol.toList) = outClass (word ++ symbol.toList) := by
  rw [toList_outClass, outClass, MultiTapeNTM.outputClass_append]
  rfl

private theorem outClass_eq_some_true {word : List Bool} :
    outClass word = some true ↔ word = [true] := by
  rw [← MultiTapeNTM.outputClass_eq_true_iff, ← toList_outClass]
  cases outClass word <;> simp

/-! ### The first phase -/

variable {S₁ S₂ : Type} {input : List Bool}

/-- The flag tape after the first machine has accepted. -/
private def flagWord : ℤ → Option Bool := Function.update (fun _ => none) 0 (some true)

/-- An action of the first machine on its block of tapes, with the output suppressed and its class
kept in the control state. A halting action that accepts writes the flag. -/
private def trackAction (o : Option Bool) (a : Turing.Action k₁ Bool S₁) :
    Turing.Action (k₁ + k₂ + 1) Bool (S₁ × Option Bool) where
  inputTape := a.inputTape
  workTapes := layout a.workTapes (fun _ => (none, 0))
    (if a.state.isNone = true ∧ outClass (o.toList ++ a.output.toList) = some true then
      (some (some true), 0) else (none, 0))
  output := none
  state := a.state.map fun q => (q, outClass (o.toList ++ a.output.toList))

/-- The first phase: run `first` on its block of tapes, tracking the class of its output instead
of writing it, and record acceptance on the flag tape. -/
private def track (first : MultiTapePTM k₁ Bool S₁) (k₂ : ℕ) :
    MultiTapePTM (k₁ + k₂ + 1) Bool (S₁ × Option Bool) where
  initial := (first.initial, none)
  tr q symbol work answer bit :=
    match first.tr q.1 symbol (fun i => work (tape₁ k₂ i)) answer bit with
    | .step a querySymbol move => .step (trackAction q.2 a) querySymbol move
    | .query op _ => op.elim

/-- The flag tape left by the first phase on reaching `c`: set exactly when `c` has halted with
output `[true]`. -/
private def flagOf (c : Cfg k₁ Bool S₁ input) : ℤ → Option Bool :=
  if c.state.isNone = true ∧ c.output = [true] then flagWord else fun _ => none

/-- A configuration of the first machine as a configuration of the first phase. -/
private def embed₁ (k₂ : ℕ) (c : Cfg k₁ Bool S₁ input) :
    Cfg (k₁ + k₂ + 1) Bool (S₁ × Option Bool) input where
  state := c.state.map fun q => (q, outClass c.output)
  inputPos := c.inputPos
  workTapes := layout c.workTapes (fun _ _ => none) (flagOf c)
  workTapePos := layout c.workTapePos (fun _ => 0) 0
  output := []

private theorem workTapeSymbols_embed₁ (c : Cfg k₁ Bool S₁ input) (i : Fin k₁) :
    (embed₁ k₂ c).workTapeSymbols (tape₁ k₂ i) = c.workTapeSymbols i := by
  simp [Cfg.workTapeSymbols, embed₁]

private theorem apply_trackAction (c : Cfg k₁ Bool S₁ input) (hc : c.state.isSome = true)
    (a : Turing.Action k₁ Bool S₁) :
    (trackAction (k₂ := k₂) (outClass c.output) a).apply (embed₁ k₂ c) = embed₁ k₂ (a.apply c) := by
  have hnone : c.state.isNone = false := by simpa [Option.isNone_iff_eq_none,
    Option.isSome_iff_ne_none] using hc
  refine Cfg.ext ?_ rfl ?_ ?_ ?_
  · simp [trackAction, embed₁, outClass_append]
  · apply funext_layout
    · intro i
      simp [trackAction, embed₁, Turing.Action.apply_workTapes]
    · intro j
      simp [trackAction, embed₁, Turing.Action.apply_workTapes]
    · simp only [trackAction, embed₁, flagOf, Turing.Action.apply_workTapes, layout_flagTape,
        hnone, Bool.false_eq_true, false_and, ite_false, Turing.Action.apply_state,
        Turing.Action.apply_output, outClass_append, outClass_eq_some_true]
      split_ifs <;> rfl
  · apply funext_layout <;> simp only [trackAction, embed₁, Turing.Action.apply_workTapePos,
      layout_tape₁, layout_tape₂, layout_flagTape] <;> (try split_ifs) <;> simp
  · simp [trackAction, embed₁]

/-- Lift a map of tapes to configurations without oracle channels. -/
private def liftCfg {k k' : ℕ} {S S' : Type} (f : Cfg k Bool S input → Cfg k' Bool S' input)
    (c : Config k Bool S Empty input) : Config k' Bool S' Empty input :=
  { tapes := f c.tapes }

private theorem step_track (first : MultiTapePTM k₁ Bool S₁) (bit : Bool)
    (c : Config k₁ Bool S₁ Empty input) :
    ((track first k₂).withCoin bit).step (liftCfg (embed₁ k₂) c) =
      liftCfg (embed₁ k₂) ((first.withCoin bit).step c) := by
  rw [Config.eq_iff_tapes_eq]
  cases hs : c.tapes.state with
  | none => simp [MultiTapeMachine.step, liftCfg, embed₁, hs]
  | some q =>
    have hans : (liftCfg (embed₁ k₂) c).answerSymbols = c.answerSymbols := Subsingleton.elim _ _
    have hwork : (fun i => (liftCfg (embed₁ k₂) c).tapes.workTapeSymbols (tape₁ k₂ i)) =
        c.tapes.workTapeSymbols := funext fun i => workTapeSymbols_embed₁ c.tapes i
    have hstate : (liftCfg (embed₁ k₂) c).tapes.state = some (q, outClass c.tapes.output) := by
      simp [liftCfg, embed₁, hs]
    have hinput : (liftCfg (embed₁ k₂) c).tapes.inputSymbol = c.tapes.inputSymbol := rfl
    simp only [MultiTapeMachine.step, hstate, hs, withCoin, track, hans, hwork, hinput]
    cases first.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
    | step a querySymbol move =>
      exact apply_trackAction c.tapes (by simp [hs]) a
    | query op _ => exact op.elim

/-! ### The second phase -/

/-- Read the flag: accept if it is set, and otherwise start rewinding the input head. -/
private def checkAction (flag : Option Bool) : Turing.Action (k₁ + k₂ + 1) Bool (Bool ⊕ S₂) :=
  if flag = some true then
    { inputTape := 0, workTapes := fun _ => (none, 0), output := some true, state := none }
  else
    { inputTape := -1, workTapes := fun _ => (none, 0), output := none, state := some (.inl true) }

/-- Move the input head left until it reads the left end marker, then step onto the first input
symbol and start the second machine. -/
private def rewindAction (initial : S₂) (symbol : Option Bool) :
    Turing.Action (k₁ + k₂ + 1) Bool (Bool ⊕ S₂) :=
  match symbol with
  | none =>
    { inputTape := 1, workTapes := fun _ => (none, 0), output := none,
      state := some (.inr initial) }
  | some _ =>
    { inputTape := -1, workTapes := fun _ => (none, 0), output := none, state := some (.inl true) }

/-- An action of the second machine on its block of tapes. -/
private def secondAction (a : Turing.Action k₂ Bool S₂) :
    Turing.Action (k₁ + k₂ + 1) Bool (Bool ⊕ S₂) where
  inputTape := a.inputTape
  workTapes := layout (fun _ => (none, 0)) a.workTapes (none, 0)
  output := a.output
  state := a.state.map .inr

/-- The second phase: accept if the flag is set, and otherwise rewind the input head and run
`second` on its block of tapes. -/
private def cont (second : MultiTapePTM k₂ Bool S₂) (k₁ : ℕ) :
    MultiTapePTM (k₁ + k₂ + 1) Bool (Bool ⊕ S₂) where
  initial := .inl false
  tr q symbol work answer bit := match q with
    | .inl false => .step (checkAction (work (flagTape k₁ k₂))) Empty.elim Empty.elim
    | .inl true => .step (rewindAction second.initial symbol) Empty.elim Empty.elim
    | .inr q => match second.tr q symbol (fun j => work (tape₂ k₁ j)) answer bit with
      | .step a querySymbol move => .step (secondAction a) querySymbol move
      | .query op _ => op.elim

/-- A configuration of the second machine as one of the second phase, with the first block of
tapes and the flag tape frozen. -/
private def embed₂ (W : Fin k₁ → ℤ → Option Bool) (P : Fin k₁ → ℤ) (F : ℤ → Option Bool)
    (c : Cfg k₂ Bool S₂ input) : Cfg (k₁ + k₂ + 1) Bool (Bool ⊕ S₂) input where
  state := c.state.map .inr
  inputPos := c.inputPos
  workTapes := layout W c.workTapes F
  workTapePos := layout P c.workTapePos 0
  output := c.output

/-- A control configuration of the second phase, before the second machine starts. -/
private def ctrl (W : Fin k₁ → ℤ → Option Bool) (P : Fin k₁ → ℤ) (F : ℤ → Option Bool)
    (state : Option Bool) (pos : Fin (input.length + 2)) (out : List Bool) :
    Cfg (k₁ + k₂ + 1) Bool (Bool ⊕ S₂) input where
  state := state.map .inl
  inputPos := pos
  workTapes := layout W (fun _ _ => none) F
  workTapePos := layout P (fun _ => 0) 0
  output := out

variable (W : Fin k₁ → ℤ → Option Bool) (P : Fin k₁ → ℤ) (F : ℤ → Option Bool)

private theorem apply_secondAction (c : Cfg k₂ Bool S₂ input) (a : Turing.Action k₂ Bool S₂) :
    (secondAction (k₁ := k₁) a).apply (embed₂ W P F c) = embed₂ W P F (a.apply c) := by
  refine Cfg.ext ?_ rfl ?_ ?_ ?_
  · simp [secondAction, embed₂]
  · apply funext_layout <;> simp [secondAction, embed₂, Turing.Action.apply_workTapes]
  · apply funext_layout <;> simp [secondAction, embed₂]
  · simp [secondAction, embed₂]

private theorem step_cont_embed₂ (second : MultiTapePTM k₂ Bool S₂) (bit : Bool)
    (c : Config k₂ Bool S₂ Empty input) :
    ((cont second k₁).withCoin bit).step (liftCfg (embed₂ W P F) c) =
      liftCfg (embed₂ W P F) ((second.withCoin bit).step c) := by
  rw [Config.eq_iff_tapes_eq]
  cases hs : c.tapes.state with
  | none => simp [MultiTapeMachine.step, liftCfg, embed₂, hs]
  | some q =>
    have hans : (liftCfg (embed₂ W P F) c).answerSymbols = c.answerSymbols :=
      Subsingleton.elim _ _
    have hwork : (fun j => (liftCfg (embed₂ W P F) c).tapes.workTapeSymbols (tape₂ k₁ j)) =
        c.tapes.workTapeSymbols := funext fun j => by simp [liftCfg, embed₂, Cfg.workTapeSymbols]
    have hstate : (liftCfg (embed₂ W P F) c).tapes.state = some (.inr q) := by
      simp [liftCfg, embed₂, hs]
    have hinput : (liftCfg (embed₂ W P F) c).tapes.inputSymbol = c.tapes.inputSymbol := rfl
    simp only [MultiTapeMachine.step, hstate, hs, withCoin, cont, hans, hwork, hinput]
    cases second.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
    | step a querySymbol move => exact apply_secondAction W P F c.tapes a
    | query op _ => exact op.elim

private theorem step_cont_check (second : MultiTapePTM k₂ Bool S₂) (bit : Bool)
    (pos : Fin (input.length + 2)) (out : List Bool) :
    ((cont second k₁).withCoin bit).step
        ({ tapes := ctrl W P F (some false) pos out } : Config _ Bool _ Empty input) =
      { tapes := if F 0 = some true then ctrl W P F none pos (out ++ [true])
          else ctrl W P F (some true) (moveInputPos pos (-1)) out } := by
  rw [Config.eq_iff_tapes_eq]
  have hflag : (ctrl (S₂ := S₂) W P F (some false) pos out).workTapeSymbols (flagTape k₁ k₂) =
      F 0 := by
    simp [ctrl, Cfg.workTapeSymbols]
  change (checkAction ((ctrl (S₂ := S₂) W P F (some false) pos out).workTapeSymbols
    (flagTape k₁ k₂))).apply _ = _
  rw [hflag, checkAction]
  split_ifs <;> refine Cfg.ext rfl ?_ ?_ ?_ ?_ <;> simp [ctrl, Turing.Action.apply_workTapes]

private theorem step_cont_rewind (second : MultiTapePTM k₂ Bool S₂) (bit : Bool)
    (pos : Fin (input.length + 2)) (out : List Bool) :
    ((cont second k₁).withCoin bit).step
        ({ tapes := ctrl W P F (some true) pos out } : Config _ Bool _ Empty input) =
      match (ctrl (k₂ := k₂) (S₂ := S₂) W P F (some true) pos out).inputSymbol with
      | none => { tapes := embed₂ W P F (Cfg.mk (some second.initial) (moveInputPos pos 1)
          (fun _ _ => none) (fun _ => 0) out) }
      | some _ => { tapes := ctrl W P F (some true) (moveInputPos pos (-1)) out } := by
  rw [Config.eq_iff_tapes_eq]
  change (rewindAction second.initial
    (ctrl (k₂ := k₂) (S₂ := S₂) W P F (some true) pos out).inputSymbol).apply _ = _
  cases (ctrl (k₂ := k₂) (S₂ := S₂) W P F (some true) pos out).inputSymbol <;>
    refine Cfg.ext rfl rfl ?_ ?_ ?_ <;> simp [ctrl, embed₂, rewindAction,
      Turing.Action.apply_workTapes]

/-- Rewinding from input position `q` takes `q + 1` steps and starts the second machine on the
first input symbol. -/
private theorem eval_cont_rewind (second : MultiTapePTM k₂ Bool S₂) (out : List Bool) (m : ℕ) :
    ∀ (q : ℕ) (pos : Fin (input.length + 2)), pos.val = q → q ≤ input.length →
      ProbComp.eval ((cont second k₁).runClosedConfigFrom (m + (q + 1))
        { tapes := ctrl W P F (some true) pos out }) =
      ProbComp.eval ((cont second k₁).runClosedConfigFrom m
        { tapes := embed₂ W P F (Cfg.mk (some second.initial) 1 (fun _ _ => none) (fun _ => 0)
          out) })
  | 0, pos, hpos, _ => by
    obtain rfl : pos = 0 := Fin.ext hpos
    rw [eval_runClosedConfigFrom_succ_of_step _ fun bit => step_cont_rewind W P F second bit 0 out]
    have hsym : (ctrl (k₂ := k₂) (S₂ := S₂) W P F (some true) (0 : Fin (input.length + 2))
        out).inputSymbol = none := by
      simp [Cfg.inputSymbol, ctrl]
    have hmove : moveInputPos (0 : Fin (input.length + 2)) 1 = 1 := by
      apply Fin.ext
      simp [moveInputPos]
    rw [hsym]
    dsimp only
    rw [hmove]
  | q + 1, pos, hpos, hq => by
    rw [show m + (q + 1 + 1) = m + (q + 1) + 1 from rfl,
      eval_runClosedConfigFrom_succ_of_step _ fun bit => step_cont_rewind W P F second bit pos out]
    have hsym : (ctrl (k₂ := k₂) (S₂ := S₂) W P F (some true) pos out).inputSymbol =
        some input[q] := inputSymbolInner q (by simp [ctrl, hpos]; omega) (by omega)
    have hne : pos ≠ 0 := fun h => by simp [h] at hpos
    rw [hsym]
    dsimp only
    exact eval_cont_rewind second out m q _
      (by
        rw [show (-1 : SignType) = .neg from rfl, moveInputPos_neg_of_ne_left pos hne]
        simp [hpos])
      (by omega)

/-- If the flag is set, the second phase accepts in one step. -/
private theorem eval_cont_of_flag (second : MultiTapePTM k₂ Bool S₂) (hF : F 0 = some true)
    (pos : Fin (input.length + 2)) (out : List Bool) (m : ℕ) :
    ProbComp.eval ((cont second k₁).runClosedConfigFrom (m + 1)
        { tapes := ctrl W P F (some false) pos out }) =
      PMF.pure { tapes := ctrl W P F none pos (out ++ [true]) } := by
  rw [eval_runClosedConfigFrom_succ_of_step _ fun bit => step_cont_check W P F second bit pos out,
    ite_eq_left hF, runClosedConfigFrom, MultiTapePTM.runConfigFrom,
    MultiTapeMachine.runConfigFrom_halted _ _ _ _ _ rfl]
  rfl

/-- If the flag is not set, the second phase rewinds the input head and then runs `second`. -/
private theorem eval_cont_of_not_flag (second : MultiTapePTM k₂ Bool S₂) (hF : F 0 ≠ some true)
    (pos : Fin (input.length + 2)) (t : ℕ)
    (ht : ∀ final ∈ (ProbComp.eval
      (second.runClosedConfigFrom t (second.initialConfig input))).support,
      final.tapes.state = none) :
    ProbComp.eval ((cont second k₁).runClosedConfigFrom (input.length + 2 + t)
        { tapes := ctrl W P F (some false) pos [] }) =
      (ProbComp.eval (second.runClosedConfigFrom t (second.initialConfig input))).map
        (liftCfg (embed₂ W P F)) := by
  set q := (moveInputPos pos (-1)).val with hq
  have hqle : q ≤ input.length := by
    have := val_moveInputPos_eq pos (-1)
    have := pos.isLt
    simp only [SignType.cast] at *
    omega
  rw [show input.length + 2 + t = t + (input.length - q) + (q + 1) + 1 by omega,
    eval_runClosedConfigFrom_succ_of_step _ fun bit => step_cont_check W P F second bit pos [],
    ite_eq_right hF, eval_cont_rewind W P F second [] _ q _ hq.symm hqle]
  change ProbComp.eval ((cont second k₁).runClosedConfigFrom _
    (liftCfg (embed₂ W P F) (second.initialConfig input))) = _
  rw [eval_runClosedConfigFrom_map second (cont second k₁) _ (step_cont_embed₂ W P F second),
    eval_runClosedConfigFrom_eq_of_halted second _ (Nat.le_add_right _ _) ht]

/-- What the second phase does after the first machine halted in `c`: accept if `c` accepted,
and otherwise run `second`. -/
private noncomputable def contResult (second : MultiTapePTM k₂ Bool S₂) (t : ℕ)
    (c : Config k₁ Bool S₁ Empty input) : PMF (Config (k₁ + k₂ + 1) Bool (Bool ⊕ S₂) Empty input) :=
  if c.tapes.output = [true] then
    PMF.pure
      { tapes :=
          ctrl c.tapes.workTapes c.tapes.workTapePos (flagOf c.tapes) none c.tapes.inputPos
            [true] }
  else
    (ProbComp.eval (second.runClosedConfigFrom t (second.initialConfig input))).map
      (liftCfg (embed₂ c.tapes.workTapes c.tapes.workTapePos (flagOf c.tapes)))

private theorem eval_cont_start (second : MultiTapePTM k₂ Bool S₂) (t : ℕ)
    (ht : ∀ final ∈ (ProbComp.eval
      (second.runClosedConfigFrom t (second.initialConfig input))).support,
      final.tapes.state = none)
    (c : Config k₁ Bool S₁ Empty input) (hc : c.tapes.state = none) :
    ProbComp.eval ((cont second k₁).runClosedConfigFrom (input.length + 2 + t)
      (Sequential.start (cont second k₁) (liftCfg (embed₁ k₂) c))) = contResult second t c := by
  change ProbComp.eval ((cont second k₁).runClosedConfigFrom _
    { tapes := ctrl c.tapes.workTapes c.tapes.workTapePos (flagOf c.tapes) (some false)
        c.tapes.inputPos [] }) = _
  unfold contResult
  split_ifs with hacc
  · rw [show input.length + 2 + t = input.length + 1 + t + 1 by omega]
    exact eval_cont_of_flag _ _ _ second (by simp [flagOf, hc, hacc, flagWord]) _ _ _
  · exact eval_cont_of_not_flag _ _ _ second (by simp [flagOf, hacc]) _ t ht

private theorem halted_of_mem_support_contResult (second : MultiTapePTM k₂ Bool S₂) (t : ℕ)
    (ht : ∀ final ∈ (ProbComp.eval
      (second.runClosedConfigFrom t (second.initialConfig input))).support,
      final.tapes.state = none)
    (c : Config k₁ Bool S₁ Empty input) {final} (hfinal : final ∈ (contResult second t c).support) :
    final.tapes.state = none := by
  unfold contResult at hfinal
  split_ifs at hfinal
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hfinal
    subst hfinal
    rfl
  · obtain ⟨c₂, hc₂, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    simp [liftCfg, embed₂, ht c₂ hc₂]

end OrElse

variable {k₁ k₂ : ℕ} {S₁ S₂ : Type}

/-- **Run a second machine if the first does not accept.** The machine runs `first` on its own
work tapes, with its output suppressed and summarized in the control state. If `first` halts
with output `[true]`, it outputs `true` and halts. Otherwise it moves the input head back to the
first input symbol and runs `second` on fresh work tapes, with fresh coins. One additional work
tape holds a flag recording the outcome of `first`. -/
noncomputable def orElse (first : MultiTapePTM k₁ Bool S₁) (second : MultiTapePTM k₂ Bool S₂) :
    MultiTapePTM (k₁ + k₂ + 1) Bool ((S₁ × Option Bool) ⊕ (Bool ⊕ S₂)) :=
  (OrElse.track first k₂).seq (OrElse.cont second k₁)

namespace OrElse

variable (first : MultiTapePTM k₁ Bool S₁) (second : MultiTapePTM k₂ Bool S₂)
  (input : List Bool)

private theorem initialConfig_orElse :
    (first.orElse second).initialConfig input = Sequential.left (cont second k₁)
      (liftCfg (embed₁ k₂) (first.initialConfig input)) := by
  rw [Config.eq_iff_tapes_eq]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · apply funext_layout <;> simp [liftCfg, embed₁, flagOf, initialConfig, Sequential.left,
      Cfg.mapState]
  · apply funext_layout <;> simp [liftCfg, embed₁, initialConfig, Sequential.left, Cfg.mapState]

/-- The configuration distribution of `first.orElse second`. -/
private theorem eval_runClosedConfigFrom_orElse (t₁ t₂ : ℕ)
    (h₁ : ∀ final ∈ (ProbComp.eval
      (first.runClosedConfigFrom t₁ (first.initialConfig input))).support,
      final.tapes.state = none)
    (h₂ : ∀ final ∈ (ProbComp.eval
      (second.runClosedConfigFrom t₂ (second.initialConfig input))).support,
      final.tapes.state = none) :
    ProbComp.eval ((first.orElse second).runClosedConfigFrom (t₁ + (input.length + 2 + t₂))
      ((first.orElse second).initialConfig input)) =
      (ProbComp.eval (first.runClosedConfigFrom t₁ (first.initialConfig input))).bind
        fun c => (contResult second t₂ c).map Sequential.right := by
  have hP1 := eval_runClosedConfigFrom_map first (track first k₂) _ (step_track first) t₁
    (first.initialConfig input)
  rw [initialConfig_orElse, orElse, eval_runClosedConfigFrom_seq _ _ _ t₁ _ ?hfirst ?hsecond,
    hP1, Probability.PMF.monad_bind_eq_bind, PMF.bind_map]
  case hfirst =>
    intro r hr
    rw [hP1] at hr
    obtain ⟨c, hc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    simp [liftCfg, embed₁, h₁ c hc]
  case hsecond =>
    intro r hr final hfinal
    rw [hP1] at hr
    obtain ⟨c, hc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    rw [eval_cont_start second t₂ h₂ c (h₁ c hc)] at hfinal
    exact halted_of_mem_support_contResult second t₂ h₂ c hfinal
  apply Probability.PMF.bind_congr_on_support
  intro c hc
  simp only [Function.comp_apply]
  rw [eval_cont_start second t₂ h₂ c (h₁ c hc)]

/-! ### Space -/

/-- The configuration of a machine after replaying `coins` from its initial configuration. -/
private abbrev reach {k : ℕ} {S : Type} (M : MultiTapePTM k Bool S) (input : List Bool)
    (coins : List Bool) : Config k Bool S Empty input :=
  M.runClosedConfigFromCoins coins (M.initialConfig input)

private theorem reach_append {k : ℕ} {S : Type} (M : MultiTapePTM k Bool S) (coins : List Bool)
    (bit : Bool) : reach M input (coins ++ [bit]) = (M.withCoin bit).step (reach M input coins) :=
  List.foldl_append ..

/-- Every configuration reachable by `first.orElse second`, phase by phase: the first phase, the
control states of the second phase, its accepting halt, and the second machine. -/
private def Reachable
    (c : Config (k₁ + k₂ + 1) Bool ((S₁ × Option Bool) ⊕ (Bool ⊕ S₂)) Empty input) : Prop :=
  (∃ coins, c = Sequential.left (cont second k₁) (liftCfg (embed₁ k₂) (reach first input coins)))
  ∨ (∃ coins W F b pos, c = Sequential.right
      { tapes := ctrl W (reach first input coins).tapes.workTapePos F (some b) pos [] } ∧
      (b = true → pos.val ≤ input.length))
  ∨ (∃ coins W F pos out, c = Sequential.right
      { tapes := ctrl W (reach first input coins).tapes.workTapePos F none pos out })
  ∨ (∃ coins W F coins₂, c = Sequential.right (liftCfg
      (embed₂ W (reach first input coins).tapes.workTapePos F) (reach second input coins₂)))

private theorem reachable_ctrl_step (bit : Bool) (coins : List Bool) (W : Fin k₁ → ℤ → Option Bool)
    (F : ℤ → Option Bool) (b : Bool) (pos : Fin (input.length + 2))
    (hpos : b = true → pos.val ≤ input.length) :
    Reachable first second input (((first.orElse second).withCoin bit).step (Sequential.right
      { tapes := ctrl W (reach first input coins).tapes.workTapePos F (some b) pos [] })) := by
  rw [orElse, step_withCoin_seq_right]
  cases b with
  | false =>
    rw [step_cont_check]
    split_ifs
    · exact Or.inr (Or.inr (Or.inl ⟨coins, W, F, pos, _, rfl⟩))
    · refine Or.inr (Or.inl ⟨coins, W, F, true, _, rfl, fun _ => ?_⟩)
      have := val_moveInputPos_eq pos (-1)
      have := pos.isLt
      simp only [SignType.cast] at *
      omega
  | true =>
    rw [step_cont_rewind]
    by_cases h0 : pos = 0
    · subst h0
      have hsym : (ctrl (k₂ := k₂) (S₂ := S₂) W (reach first input coins).tapes.workTapePos F
          (some true) (0 : Fin (input.length + 2)) []).inputSymbol = none := by
        simp [Cfg.inputSymbol, ctrl]
      have hmove : moveInputPos (0 : Fin (input.length + 2)) 1 = 1 := by
        apply Fin.ext
        simp [moveInputPos]
      rw [hsym]
      dsimp only
      rw [hmove]
      exact Or.inr (Or.inr (Or.inr ⟨coins, W, F, [], rfl⟩))
    · have hp := hpos rfl
      have hval : pos.val = 1 + (pos.val - 1) := by
        have : pos.val ≠ 0 := fun h => h0 (Fin.ext h)
        omega
      have hsym : (ctrl (k₂ := k₂) (S₂ := S₂) W (reach first input coins).tapes.workTapePos F
          (some true) pos []).inputSymbol = some input[pos.val - 1] :=
        inputSymbolInner _ hval (by omega)
      rw [hsym]
      dsimp only
      refine Or.inr (Or.inl ⟨coins, W, F, true, _, rfl, fun _ => ?_⟩)
      rw [show (-1 : SignType) = .neg from rfl, moveInputPos_neg_of_ne_left pos h0]
      simp only
      omega

private theorem reachable_step (bit : Bool) {c} (hc : Reachable first second input c) :
    Reachable first second input (((first.orElse second).withCoin bit).step c) := by
  rcases hc with ⟨coins, rfl⟩ | ⟨coins, W, F, b, pos, rfl, hpos⟩ | ⟨coins, W, F, pos, out, rfl⟩ |
    ⟨coins, W, F, coins₂, rfl⟩
  · by_cases hrun : (reach first input coins).tapes.state = none
    · rw [Sequential.left_halted _ _ (by simp [liftCfg, embed₁, hrun])]
      exact reachable_ctrl_step first second input bit coins _ _ false _ (by simp)
    · left
      refine ⟨coins ++ [bit], ?_⟩
      rw [orElse, step_withCoin_seq_left _ _ _ _ (by simpa [liftCfg, embed₁] using hrun),
        step_track, reach_append]
  · exact reachable_ctrl_step first second input bit coins W F b pos hpos
  · right; right; left
    refine ⟨coins, W, F, pos, out, ?_⟩
    simp [MultiTapeMachine.step, Sequential.right, Cfg.mapState, ctrl]
  · right; right; right
    refine ⟨coins, W, F, coins₂ ++ [bit], ?_⟩
    rw [orElse, step_withCoin_seq_right, step_cont_embed₂, reach_append]

private theorem reachable_runClosedConfigFromCoins (coins : List Bool) :
    ∀ c, Reachable first second input c →
      Reachable first second input ((first.orElse second).runClosedConfigFromCoins coins c) := by
  induction coins with
  | nil => exact fun _ hc => hc
  | cons bit coins ih => exact fun c hc => ih _ (reachable_step first second input bit hc)

private theorem reachable_initialConfig :
    Reachable first second input ((first.orElse second).initialConfig input) :=
  Or.inl ⟨[], initialConfig_orElse first second input⟩

private theorem workTapePos_mem_window {k : ℕ} {S : Type} (M : MultiTapePTM k Bool S) {s : ℕ}
    (hs : M.toNTM.RunsInSpace input s) (coins : List Bool) (i : Fin k) :
    (reach M input coins).tapes.workTapePos i ∈ window s := by
  obtain ⟨p, hhead, -, hlast⟩ := (M.exists_runPath_toNTM_iff (c := M.toNTM.initCfg input)).mpr
    ⟨coins, rfl, rfl⟩
  have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le (p := p) (s := s)
    (fun i => by rw [hhead]; rfl) (hs ⟨p, hhead⟩)
  rw [reach, tapes_runClosedConfigFromCoins, ← initCfg_toNTM, ← hlast]
  exact hwin _ p.last_mem i

private theorem forall_layout {p : Fin (k₁ + k₂ + 1) → Prop} (h₁ : ∀ i, p (tape₁ k₂ i))
    (h₂ : ∀ j, p (tape₂ k₁ j)) (hf : p (flagTape k₁ k₂)) (i : Fin (k₁ + k₂ + 1)) : p i := by
  refine Fin.addCases (fun i => Fin.addCases (fun i => h₁ i) (fun j => h₂ j) i) (fun i => ?_) i
  rwa [Fin.fin_one_eq_zero i]

private theorem workTapePos_mem_window_of_reachable {s₁ s₂ : ℕ}
    (hs₁ : first.toNTM.RunsInSpace input s₁) (hs₂ : second.toNTM.RunsInSpace input s₂) {c}
    (hc : Reachable first second input c) (i : Fin (k₁ + k₂ + 1)) :
    c.tapes.workTapePos i ∈ window (max s₁ s₂) := by
  have hmono {s s' : ℕ} {z : ℤ} (h : z ∈ window s) (hle : s ≤ s') : z ∈ window s' :=
    mem_window.mpr ((mem_window.mp h).trans hle)
  have hzero : (0 : ℤ) ∈ window (max s₁ s₂) := by simp [mem_window]
  have h₁ (coins : List Bool) (i : Fin k₁) :
      (reach first input coins).tapes.workTapePos i ∈ window (max s₁ s₂) :=
    hmono (workTapePos_mem_window input first hs₁ coins i) (le_max_left _ _)
  have h₂ (coins : List Bool) (j : Fin k₂) :
      (reach second input coins).tapes.workTapePos j ∈ window (max s₁ s₂) :=
    hmono (workTapePos_mem_window input second hs₂ coins j) (le_max_right _ _)
  rcases hc with ⟨coins, rfl⟩ | ⟨coins, W, F, b, pos, rfl, -⟩ | ⟨coins, W, F, pos, out, rfl⟩ |
    ⟨coins, W, F, coins₂, rfl⟩
  · revert i
    refine forall_layout ?_ ?_ ?_ <;>
      simp [Sequential.left, Cfg.mapState, liftCfg, embed₁, h₁, hzero]
  · revert i
    refine forall_layout ?_ ?_ ?_ <;> simp [Sequential.right, Cfg.mapState, ctrl, h₁, hzero]
  · revert i
    refine forall_layout ?_ ?_ ?_ <;> simp [Sequential.right, Cfg.mapState, ctrl, h₁, hzero]
  · revert i
    refine forall_layout ?_ ?_ ?_ <;>
      simp [Sequential.right, Cfg.mapState, liftCfg, embed₂, h₁, h₂, hzero]

end OrElse

/-- **Space of `first.orElse second`.** If every computation path of `first` and of `second`
visits at most `s₁` and `s₂` work-tape cells, then every head of the combined machine stays in the
window `[-max s₁ s₂, max s₁ s₂]`, so each of its `k₁ + k₂ + 1` work tapes uses at most
`2 * max s₁ s₂ + 1` cells. -/
theorem runsInSpace_toNTM_orElse {k₁ k₂ : ℕ} {S₁ S₂ : Type} (first : MultiTapePTM k₁ Bool S₁)
    (second : MultiTapePTM k₂ Bool S₂) {input : List Bool} {s₁ s₂ : ℕ}
    (hs₁ : first.toNTM.RunsInSpace input s₁) (hs₂ : second.toNTM.RunsInSpace input s₂) :
    (first.orElse second).toNTM.RunsInSpace input ((k₁ + k₂ + 1) * (2 * max s₁ s₂ + 1)) := by
  intro p
  apply MultiTapeNTM.RunPath.InWindow.space_le
  rintro _ ⟨j, rfl⟩ i
  obtain ⟨coins, -, hcoins⟩ := ((first.orElse second).exists_runPath_toNTM_iff).mp
    ⟨p.toRunPath.take j, RelSeries.head_take _ _, rfl,
      RelSeries.last_take _ _⟩
  rw [← hcoins, p.head_eq, initCfg_toNTM, ← tapes_runClosedConfigFromCoins]
  exact OrElse.workTapePos_mem_window_of_reachable first second input hs₁ hs₂
    (OrElse.reachable_runClosedConfigFromCoins first second input coins _
      (OrElse.reachable_initialConfig first second input)) i

section Main

variable {k₁ k₂ : ℕ} {S₁ S₂ : Type} (first : MultiTapePTM k₁ Bool S₁)
  (second : MultiTapePTM k₂ Bool S₂) (input : List Bool) (t₁ t₂ : ℕ)
  (h₁ : ∀ final ∈ (ProbComp.eval
    (first.runClosedConfigFrom t₁ (first.initialConfig input))).support,
    final.tapes.state = none)
  (h₂ : ∀ final ∈ (ProbComp.eval
    (second.runClosedConfigFrom t₂ (second.initialConfig input))).support,
    final.tapes.state = none)

include h₁ h₂

/-- `first.orElse second` halts on every branch within `t₁ + (n + 2 + t₂)` steps when `first`
halts within `t₁` and `second` within `t₂` steps, where `n` is the input length. -/
theorem orElse_halted :
    ∀ final ∈ (ProbComp.eval ((first.orElse second).runClosedConfigFrom
      (t₁ + (input.length + 2 + t₂)) ((first.orElse second).initialConfig input))).support,
      final.tapes.state = none := by
  intro final hfinal
  rw [OrElse.eval_runClosedConfigFrom_orElse first second input t₁ t₂ h₁ h₂] at hfinal
  obtain ⟨c, -, hc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
  obtain ⟨d, hd, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  change (d.tapes.state).map Sum.inr = none
  rw [OrElse.halted_of_mem_support_contResult second t₂ h₂ c hd]
  rfl

/-- **The output distribution of `first.orElse second`**: run `first`; if it outputs `[true]`,
output `[true]`, and otherwise run `second` with fresh coins. Both machines must halt on every
branch within their clocks. -/
theorem eval_runClosed_orElse :
    ProbComp.eval ((first.orElse second).runClosed (t₁ + (input.length + 2 + t₂)) input) =
      (do
        let word ← ProbComp.eval (first.runClosed t₁ input)
        if word = [true] then pure [true] else ProbComp.eval (second.runClosed t₂ input)) := by
  rw [runClosed_eq_map, ProbComp.eval_map,
    OrElse.eval_runClosedConfigFrom_orElse first second input t₁ t₂ h₁ h₂, runClosed_eq_map,
    ProbComp.eval_map, Probability.PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind]
  congr 1
  funext c
  simp only [Function.comp_apply, OrElse.contResult, PMF.map_comp]
  split_ifs with hacc
  · rw [PMF.pure_map]
    rfl
  · rw [runClosed_eq_map, ProbComp.eval_map, PMF.map_comp]
    rfl

end Main

end Turing.MultiTapePTM
