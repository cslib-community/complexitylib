/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy.Redirect

import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Tidy combinators for probabilistic oracle machines

This module lifts the deterministic tidy-machine combinators (`comp`, `append`, and `branch`/`ite`)
to `MultiTapePTM` specifications in `RunsWords` and `ComputesTidily`, re-exporting the foundational
phase specifications (`RunsWords`) and word-redirection combinators (`Tidy/Redirect`). Every
combinator preserves the exact joint distribution of tape words, emitted output and external oracle
state, and maintains clean query buffers at phase boundaries.

## Main definitions

* `Turing.MultiTapePTM.tidyComp`: sequential composition of tidy probabilistic machines.
* `Turing.MultiTapePTM.appendPTM`: concatenate the outputs of two tidy probabilistic machines.
* `Turing.MultiTapePTM.branch`: branch on whether a work tape is blank without executing the
  unselected branch.
* `Turing.MultiTapePTM.itePTM`: tidy case distinction on a work tape word.

## Main results

* `Turing.MultiTapePTM.ComputesTidily.comp`: tidy sequential composition.
* `Turing.MultiTapePTM.ComputesTidily.append`: tidy output concatenation.
* `Turing.MultiTapePTM.ComputesTidily.ite`: tidy conditional execution.

## References

Adapts the deterministic tidy-machine combinators of Christian Reitwiessner's
crei:crei/tidy-universal @7f7c0696 (`Combinators/Comp`, `Combinators/Append`, and `Combinators/Ite`)
to the probabilistic oracle machines of the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeMachine.Sequential MultiTapeTM

variable {k k₀ k₁ k₂ : ℕ} {State State₀ State₁ State₂ Operation OracleState : Type}
  {x : List Bool} [DecidableEq Operation]

/-! ### Composing tidy probabilistic machines (`tidyComp` and `appendPTM`) -/

/-- Run `tm₁` with its output written to work tape `Fin.natAdd (max k₁ k₂) 0`, then run `tm₂`
reading its input from that tape (using `mark` on the last work tape), and finally clear that
tape. -/
noncomputable def tidyComp (tm₂ : MultiTapePTM k₂ Bool State₂ Operation)
    (tm₁ : MultiTapePTM k₁ Bool State₁ Operation) (mark : Bool) :
    MultiTapePTM (max k₁ k₂ + 2) Bool
      ((State₁ ⊕ RewindWorkState) ⊕
        (MarkWorkState ⊕ State₂ ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState) Operation :=
  ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).seq
    (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
      (ofDeterministic ((clearWork Bool).extendTapes (tapeEmb (Fin.natAdd (max k₁ k₂) 0)))))

/-- If `tm₁` computes `prog₁` tidily on `x` in `t₁` steps with outputs of length at most `l`, and
`tm₂` computes `prog₂ w` tidily on every supported output `w` of `prog₁` in `t₂` steps, then
`tm₂.tidyComp tm₁ mark` computes `prog₁ >>= prog₂` tidily on `x` in `t₁ + t₂ + 4 * l + 9` steps. -/
theorem ComputesTidily.comp_of_le {tm₁ : MultiTapePTM k₁ Bool State₁ Operation}
    {tm₂ : MultiTapePTM k₂ Bool State₂ Operation} {t₁ t₂ l : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    {prog₂ : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (mark : Bool) (h₁ : tm₁.ComputesTidily x t₁ prog₁)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w : List Bool) (s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support → w.length ≤ l)
    (h₂ : ∀ w (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support → tm₂.ComputesTidily w t₂ (prog₂ w)) :
    (tm₂.tidyComp tm₁ mark).ComputesTidily x (t₁ + t₂ + 4 * l + 9) (prog₁ >>= prog₂) := by
  rw [computesTidily_iff_nil_output]
  let K := max k₁ k₂
  let A : Fin (K + 2) := Fin.natAdd K 0
  have hQ₁ (w : List Bool) :
      (fun l : Fin (K + 1 + 1) =>
        (MultiTapeTM.partialInv Fin.castSuccEmb l).elim ([] : List Bool)
          (Function.update (fun _ : Fin (K + 1) => []) (Fin.last K) w)) =
        Function.update (fun _ => []) A w := by
    funext idx
    induction idx using Fin.lastCases with
    | last =>
      rw [MultiTapeTM.partialInv_eq_none Fin.castSuccEmb
        (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)]
      simp [A, Fin.ext_iff]
    | cast j =>
      change (MultiTapeTM.partialInv Fin.castSuccEmb (Fin.castSuccEmb j)).elim _ _ = _
      rw [MultiTapeTM.partialInv_embed]
      simp [A, Function.update_apply, Fin.ext_iff]
  have hp₁ : ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).RunsWords x (fun _ => []) [] (t₁ + (l + 2)) prog₁
      (fun w => Function.update (fun _ => []) A w) (fun _ => []) := by
    have h₀ :=
      ((h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord_of_le hl []).extendTapes
        (ws₀ := fun _ => []) Fin.castSuccEmb
    rw [← funext hQ₁]
    exact h₀
  have hinj₁ : Function.Injective
      (fun w : List Bool => (Function.update (fun _ => []) A w, ([] : List Bool))) := by
    intro w₁ w₂ heq
    have hfun := congrFun (congrArg Prod.fst heq) A
    simpa only [Function.update_self] using hfun
  have hp₂₃ : ∀ w (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
        (ofDeterministic ((clearWork Bool).extendTapes (tapeEmb A)))).RunsWords
        x (Function.update (fun _ => []) A w) ([] ++ []) ((t₂ + 4) + 3 * (l + 1))
        (prog₂ w) (fun _ _ => []) id := by
    intro w OracleState oracle s s' hw
    have hwlen := hl OracleState oracle s w s' hw
    have hp₂ : ((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).RunsWords
        x (Function.update (fun _ => []) A w) [] (t₂ + 4) (prog₂ w)
        (fun _ => Function.update (fun _ => []) A w) id := by
      have h₀ := (((h₂ w OracleState oracle s s' hw).extendTapes
        (Fin.castLEEmb (le_max_right k₁ k₂))) []).inputFromWord (x := x) mark
      simpa only [append_nil_eq_update] using h₀
    have hinj₂ : Function.Injective
        (fun y : List Bool => (Function.update (fun _ => []) A w, id y)) :=
      fun _ _ heq => congrArg Prod.snd heq
    have hp₃ : ∀ y (OracleState' : Type)
        (oracle' : Operation × List Bool → StateT OracleState' PMF (List Bool))
        (s₀ s₁ : OracleState'),
        (y, s₁) ∈ ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle')
          (prog₂ w)).run s₀).support →
        (ofDeterministic (Oracle := Operation)
          ((clearWork Bool).extendTapes (tapeEmb A))).RunsWords
          x (Function.update (fun _ => []) A w) ([] ++ id y) (3 * (l + 1)) (pure ())
          (fun _ _ => []) (fun _ => []) := by
      intro y _ _ _ _ _
      exact (RunsWords.of_transformsTapes (Operation := Operation) (out₀ := [] ++ id y)
        (transformsTapes_clearWork_only A w) rfl (fun _ _ hQ => hQ)).mono
        (time' := 3 * (l + 1)) (by omega)
    have hseq := hp₂.seq_pure_right hinj₂ hp₃
    have happend : (fun a : List Bool => id a ++ []) = id := by
      funext a
      exact List.append_nil a
    simpa only [List.nil_append, happend] using hseq
  have hseq := (hp₁.seq_bind hinj₁ hp₂₃).of_map Prod.snd (fun _ _ => []) id
  have hbind : (Prod.snd <$> (prog₁ >>= fun a => (fun b => (a, b)) <$> prog₂ a)) =
      (prog₁ >>= prog₂) := by
    have hid : (fun b : List Bool => b) = id := rfl
    simp only [map_bind, Functor.map_map, hid, id_map]
  rw [hbind] at hseq
  exact hseq.mono (by omega)

/-- Unconditional tidy sequential composition using `h₁.length_output_le`. -/
theorem ComputesTidily.comp {tm₁ : MultiTapePTM k₁ Bool State₁ Operation}
    {tm₂ : MultiTapePTM k₂ Bool State₂ Operation} {t₁ t₂ : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    {prog₂ : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (mark : Bool) (h₁ : tm₁.ComputesTidily x t₁ prog₁)
    (h₂ : ∀ w (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support → tm₂.ComputesTidily w t₂ (prog₂ w)) :
    (tm₂.tidyComp tm₁ mark).ComputesTidily x (5 * t₁ + t₂ + 9) (prog₁ >>= prog₂) := by
  exact (h₁.comp_of_le mark (fun _ oracle s _ _ hw => h₁.length_output_le oracle s hw) h₂).mono
    (by omega)

/-- Run `tm₁` and then `tm₂` on the same input, both padded to `max k₁ k₂` work tapes. -/
def appendPTM (tm₁ : MultiTapePTM k₁ Bool State₁ Operation)
    (tm₂ : MultiTapePTM k₂ Bool State₂ Operation) :
    MultiTapePTM (max k₁ k₂) Bool (State₁ ⊕ State₂) Operation :=
  (tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).seq
    (tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))

/-- If `tm₁` computes `prog₁` tidily in `t₁` steps and `tm₂` computes `prog₂ w₁` tidily in `t₂`
steps on the same input `x`, then `appendPTM tm₁ tm₂` computes
`prog₁ >>= fun w₁ => (fun w₂ => w₁ ++ w₂) <$> prog₂ w₁` tidily in `t₁ + t₂` steps. -/
theorem ComputesTidily.append {tm₁ : MultiTapePTM k₁ Bool State₁ Operation}
    {tm₂ : MultiTapePTM k₂ Bool State₂ Operation} {t₁ t₂ : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    {prog₂ : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h₁ : tm₁.ComputesTidily x t₁ prog₁)
    (h₂ : ∀ w₁ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w₁, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support → tm₂.ComputesTidily x t₂ (prog₂ w₁)) :
    (appendPTM tm₁ tm₂).ComputesTidily x (t₁ + t₂)
      (prog₁ >>= fun w₁ => (fun w₂ => w₁ ++ w₂) <$> prog₂ w₁) := by
  rw [computesTidily_iff_nil_output]
  have hp₁ := (h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))) []
  have hinj : Function.Injective
      (fun w₁ : List Bool => ((fun _ : Fin (max k₁ k₂) => ([] : List Bool)), id w₁)) :=
    fun _ _ heq => congrArg Prod.snd heq
  have hp₂ : ∀ w₁ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w₁, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      (tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).RunsWords
        x (fun _ => []) ([] ++ id w₁) t₂ (prog₂ w₁) (fun _ _ => []) id :=
    fun w₁ OracleState oracle s s' hw =>
      ((h₂ w₁ OracleState oracle s s' hw).extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))
        ([] ++ id w₁)
  have hseq := (hp₁.seq_bind hinj hp₂).of_map (fun p : List Bool × List Bool => p.1 ++ p.2)
    (fun _ _ => []) id
  dsimp only [appendPTM]
  simpa only [map_bind, Functor.map_map, id_eq] using hseq

/-- Prepend a deterministically computed prefix word before a tidy probabilistic computation. -/
theorem ComputesTidily.prefix {prep : MultiTapeTM k₁ Bool State₁}
    {source : MultiTapePTM k₂ Bool State₂ Operation} {pre : List Bool} {t₁ s₁ t₂ : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (hprep : prep.ComputesTidilyInTimeAndSpace x pre t₁ s₁)
    (hsource : source.ComputesTidily x t₂ program) :
    (appendPTM (ofDeterministic prep) source).ComputesTidily x (t₁ + t₂)
      ((fun y => pre ++ y) <$> program) := by
  have h := (ComputesTidily.of_deterministic (Operation := Operation) hprep).append
    (fun _ _ _ _ _ _ => hsource)
  simpa only [pure_bind] using h

/-! ### Conditional branching (`branch` and `itePTM`) -/

/-- Read the cell under the head of work tape `i`, moving no head and writing nothing, then run
`tm₁` if the cell is not blank and `tm₂` if it is. -/
def branch (i : Fin k) (tm₁ : MultiTapePTM k Bool State₁ Operation)
    (tm₂ : MultiTapePTM k Bool State₂ Operation) :
    MultiTapePTM k Bool (Option (State₁ ⊕ State₂)) Operation where
  initial := none
  tr q inp work answer bit :=
    match q with
    | none => .step
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := some (some ((work i).elim (.inr tm₂.initial) fun _ => .inl tm₁.initial)) }
      (fun _ => none) (fun _ => 0)
    | some (.inl q) =>
      MultiTapeMachine.Action.mapState (fun s => some (Sum.inl s)) (tm₁.tr q inp work answer bit)
    | some (.inr q) =>
      MultiTapeMachine.Action.mapState (fun s => some (Sum.inr s)) (tm₂.tr q inp work answer bit)

namespace Branch

variable {i : Fin k} {tm₁ : MultiTapePTM k Bool State₁ Operation}
  {tm₂ : MultiTapePTM k Bool State₂ Operation}

/-- If `branch i tm₁ tm₂` acts on `f q` by mapping `tm`'s actions through `f`, then its clocked
run from `Config.mapState f cfg` maps `tm`'s clocked run through `Config.mapState f`. -/
theorem runOracleConfigFrom_mapState {S : Type} {tm : MultiTapePTM k Bool S Operation}
    {f : S → Option (State₁ ⊕ State₂)}
    (htr : ∀ q inp work answer bit,
      (branch i tm₁ tm₂).tr (f q) inp work answer bit =
        MultiTapeMachine.Action.mapState f (tm.tr q inp work answer bit))
    (fuel : ℕ) (cfg : Config k Bool S Operation x) :
    (branch i tm₁ tm₂).runOracleConfigFrom fuel (Config.mapState f cfg) =
      Config.mapState f <$> tm.runOracleConfigFrom fuel cfg :=
  MultiTapeMachine.runConfigFrom_mapState
    (Choose := ReaderT Bool Id)
    (spec := probOracleSpec (fun _ : Operation × List Bool => List Bool))
    tm (branch i tm₁ tm₂)
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun _ _ => by simp only [Functor.map_map]; rfl)
    (fun op word => ProbOracleComp.query (op, word)) f
    (fun q inp work answer => funext (htr q inp work answer))
    fuel cfg

end Branch

/-- When tape `i` is empty, `branch i tm₁ tm₂` transitions in `1` step to `tm₂` and never executes
`tm₁`. -/
theorem RunsWords.branch_nil (i : Fin k) (tm₁ : MultiTapePTM k Bool State₁ Operation)
    {tm₂ : MultiTapePTM k Bool State₂ Operation}
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t₂ : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (hi : ws₀ i = []) (h₂ : tm₂.RunsWords x ws₀ out₀ t₂ program ws₁ emit) :
    (branch i tm₁ tm₂).RunsWords x ws₀ out₀ (t₂ + 1) program ws₁ emit :=
  RunsWords.of_first_step_mapState (f := fun s => some (Sum.inr s))
    (fun _ _ => by simp [branch, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hi])
    (fun _ _ _ _ _ => rfl) h₂

/-- When tape `i` is non-empty, `branch i tm₁ tm₂` transitions in `1` step to `tm₁` and never
executes `tm₂`. -/
theorem RunsWords.branch_ne_nil (i : Fin k) {tm₁ : MultiTapePTM k Bool State₁ Operation}
    (tm₂ : MultiTapePTM k Bool State₂ Operation)
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t₁ : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (hi : ws₀ i ≠ []) (h₁ : tm₁.RunsWords x ws₀ out₀ t₁ program ws₁ emit) :
    (branch i tm₁ tm₂).RunsWords x ws₀ out₀ (t₁ + 1) program ws₁ emit := by
  obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hi
  exact RunsWords.of_first_step_mapState (f := fun s => some (Sum.inl s))
    (fun _ _ => by simp [branch, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hbs])
    (fun _ _ _ _ _ => rfl) h₁

/-- Run `tmc` with its output on a new last work tape, then `tm₁` if that word is non-empty and
`tm₂` otherwise, and clear the tape. -/
noncomputable def itePTM (tmc : MultiTapePTM k₀ Bool State₀ Operation)
    (tm₁ : MultiTapePTM k₁ Bool State₁ Operation)
    (tm₂ : MultiTapePTM k₂ Bool State₂ Operation) :
    MultiTapePTM (max k₀ (max k₁ k₂) + 1) Bool
      ((State₀ ⊕ RewindWorkState) ⊕
        Option (State₁ ⊕ State₂) ⊕ Unit ⊕ RewindWorkState) Operation :=
  (tmc.extendTapes (Fin.castLEEmb (le_max_left _ _))).outputToWord.seq
    ((branch (Fin.last _)
        ((tm₁.extendTapes (Fin.castLEEmb ((le_max_left k₁ k₂).trans
          (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)
        ((tm₂.extendTapes (Fin.castLEEmb ((le_max_right k₁ k₂).trans
          (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)).seq
      (ofDeterministic ((clearWork Bool).extendTapes (tapeEmb (Fin.last _)))))

/-- A tidy probabilistic machine padded to `K` work tapes and placed below a last work tape that
holds `w` throughout. -/
private theorem ComputesTidily.runsWords_padded {k K : ℕ} (hk : k ≤ K)
    {tm : MultiTapePTM k Bool State Operation} {w : List Bool} {t : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : tm.ComputesTidily x t program) :
    ((tm.extendTapes (Fin.castLEEmb hk)).extendTapes Fin.castSuccEmb).RunsWords
      x (Function.update (fun _ => []) (Fin.last K) w) [] t program
      (fun _ => Function.update (fun _ => []) (Fin.last K) w) id := by
  have hpre : (fun j : Fin K =>
      Function.update (fun _ : Fin (K + 1) => ([] : List Bool)) (Fin.last K) w
        (Fin.castSuccEmb j)) = fun _ => [] := by
    funext j
    simp [Fin.castSucc_ne_last]
  have h₀ : (tm.extendTapes (Fin.castLEEmb hk)).RunsWords x
      (fun j => Function.update (fun _ => []) (Fin.last K) w (Fin.castSuccEmb j))
      [] t program (fun _ _ => []) id := by
    rw [hpre]
    exact (h.extendTapes (Fin.castLEEmb hk)) []
  have hext := h₀.extendTapes (ws₀ := Function.update (fun _ => []) (Fin.last K) w) Fin.castSuccEmb
  have hpost : (fun (_ : List Bool) (l : Fin (K + 1)) =>
      (MultiTapeTM.partialInv Fin.castSuccEmb l).elim
        (Function.update (fun _ : Fin (K + 1) => ([] : List Bool)) (Fin.last K) w l)
        (fun _ => [])) =
      fun _ => Function.update (fun _ => []) (Fin.last K) w := by
    funext _ l
    induction l using Fin.lastCases with
    | last =>
      rw [MultiTapeTM.partialInv_eq_none Fin.castSuccEmb
        (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)]
      rfl
    | cast j =>
      change (MultiTapeTM.partialInv Fin.castSuccEmb (Fin.castSuccEmb j)).elim _ _ = _
      rw [MultiTapeTM.partialInv_embed]
      simp [Fin.castSucc_ne_last]
  simpa only [hpost] using hext

/-- If `tmc` computes the test word `w` from `x` tidily, `tm₁` computes `prog₁` tidily when
`w ≠ []` and `tm₂` computes `prog₂` tidily when `w = []`, then `itePTM tmc tm₁ tm₂` computes
`if w = [] then prog₂ else prog₁` tidily within the bounds of `tmc` plus those of the active
branch, never executing the unselected branch. -/
theorem ComputesTidily.ite {tmc : MultiTapePTM k₀ Bool State₀ Operation}
    {tm₁ : MultiTapePTM k₁ Bool State₁ Operation}
    {tm₂ : MultiTapePTM k₂ Bool State₂ Operation}
    {w : List Bool} {tc t₁ t₂ : ℕ}
    {prog₁ prog₂ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (hc : tmc.ComputesTidily x tc (pure w))
    (h₁ : w ≠ [] → tm₁.ComputesTidily x t₁ prog₁)
    (h₂ : w = [] → tm₂.ComputesTidily x t₂ prog₂) :
    (itePTM tmc tm₁ tm₂).ComputesTidily x
      (tc + (if w = [] then t₂ else t₁) + 4 * w.length + 6)
      (if w = [] then prog₂ else prog₁) := by
  rw [computesTidily_iff_nil_output]
  set K := max k₀ (max k₁ k₂)
  let clearLast : MultiTapePTM (K + 1) Bool (Unit ⊕ RewindWorkState) Operation :=
    ofDeterministic ((clearWork Bool).extendTapes (tapeEmb (Fin.last K)))
  have hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w' : List Bool) (s' : OracleState),
      (w', s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (pure w)).run s).support → w'.length ≤ w.length := by
    intro _ _ _ w' s' hw'
    simp only [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hw'
    rcases Prod.mk.inj hw' with ⟨rfl, rfl⟩
    exact le_rfl
  have hp₁ : (tmc.extendTapes (Fin.castLEEmb (le_max_left k₀ (max k₁ k₂)))).outputToWord.RunsWords
      x (fun _ => []) [] (tc + (w.length + 2)) (pure ())
      (fun _ => Function.update (fun _ => []) (Fin.last K) w) (fun _ => []) := by
    have h₀ := (hc.extendTapes (Fin.castLEEmb (le_max_left k₀ (max k₁ k₂)))).outputToWord_of_le
      hl []
    have hcongr : (tmc.extendTapes
        (Fin.castLEEmb (le_max_left k₀ (max k₁ k₂)))).outputToWord.RunsWords
        x (fun _ => []) [] (tc + (w.length + 2)) ((fun _ => w) <$> pure ())
        (fun w' => Function.update (fun _ => []) (Fin.last K) w') (fun _ => []) := by
      simpa only [map_pure] using h₀
    intro OracleState oracle s cfg htapes hbuf
    obtain ⟨hlaw, hclean⟩ := hcongr OracleState oracle s cfg htapes hbuf
    refine ⟨?_, hclean⟩
    simpa only [OracleComp.interpret_pure, OracleComp.interpret_map, StateT.run_pure,
      StateT.run_map, Probability.PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.pure_map]
      using hlaw
  have hp₂ : (branch (Fin.last K)
      ((tm₁.extendTapes (Fin.castLEEmb ((le_max_left k₁ k₂).trans
        (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)
      ((tm₂.extendTapes (Fin.castLEEmb ((le_max_right k₁ k₂).trans
        (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)).RunsWords
      x (Function.update (fun _ => []) (Fin.last K) w) []
      ((if w = [] then t₂ else t₁) + 1)
      (if w = [] then prog₂ else prog₁)
      (fun _ => Function.update (fun _ => []) (Fin.last K) w) id := by
    by_cases hw : w = []
    · simp only [hw, ↓reduceIte]
      exact RunsWords.branch_nil (Fin.last K) _ (by simp)
        ((h₂ hw).runsWords_padded ((le_max_right k₁ k₂).trans (le_max_right k₀ _)))
    · simp only [hw, ↓reduceIte]
      exact RunsWords.branch_ne_nil (Fin.last K) _ (by simp [hw])
        ((h₁ hw).runsWords_padded ((le_max_left k₁ k₂).trans (le_max_right k₀ _)))
  have hinj₂ : Function.Injective
      (fun y : List Bool => (Function.update (fun _ => []) (Fin.last K) w, id y)) :=
    fun _ _ heq => congrArg Prod.snd heq
  have hp₃ : ∀ y (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (y, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (if w = [] then prog₂ else prog₁)).run s).support →
      clearLast.RunsWords
        x (Function.update (fun _ => []) (Fin.last K) w) ([] ++ id y)
        (3 * (w.length + 1)) (pure ()) (fun _ _ => []) (fun _ => []) := by
    intro y _ _ _ _ _
    exact RunsWords.of_transformsTapes (Operation := Operation) (out₀ := [] ++ id y)
      (transformsTapes_clearWork_only (Fin.last K) w) rfl (fun _ _ hQ => hQ)
  have hp₂₃ := hp₂.seq_pure_right hinj₂ hp₃
  have happend : (fun a : List Bool => id a ++ []) = id := by
    funext a
    exact List.append_nil a
  rw [happend] at hp₂₃
  have hseq := (hp₁.seq_pure_left hp₂₃).mono
    (time' := tc + (if w = [] then t₂ else t₁) + 4 * w.length + 6)
    (by split_ifs <;> omega)
  dsimp only [itePTM]
  simpa only [List.nil_append] using hseq

end Turing.MultiTapePTM
