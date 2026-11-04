/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Bounds
import Complexity.Computability.Complexity.Classes.LogSpace.Complement

/-! Integration tests for input bootstrap, finite binary choices and looping native sources. -/

namespace ComplexityTests.NLComplement

open Turing Turing.MultiTapeTM Turing.InductiveCounting

/-- Concrete finite query models instantiate every hypothesis of the new native compiler. -/
private theorem finite_query_native {σ : Type} [Finite σ]
    (M : NondeterministicQueryMachine σ) (time : ℕ)
    (hhalt : ∀ input, M.HaltsWithin input time) {A : Set (List Bool)}
    (hcorrect : ∀ input, input ∈ A ↔ M.Accepts input) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      ntm.DecidesInSpace encBits A fun input => c * (Nat.log2 input.length + 1) := by
  apply M.exists_decidesInSpace (enc := encBits) (encS := encFinite σ)
    (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _)
    (fun _ => time) hhalt hcorrect
    (fun input : List Bool => Nat.log2 input.length + 1) (fun _ => le_rfl)
  refine ⟨Nat.card σ, fun input choices => ?_⟩
  exact (length_encFinite_lt (M.run input choices)).le.trans
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

/-- One accepting and one rejecting branch, with the input answer deliberately ignored. -/
private def branching : NondeterministicQueryMachine (Fin 3) where
  init := 0
  query _ := 0
  next p := if p.2.2 then 1 else 2
  halted q := q != 0
  accept q := q == 1

example (input : List Bool) : branching.run input [true] = 1 := rfl
example (input : List Bool) : branching.run input [false] = 2 := rfl

example (input : List Bool) : branching.Accepts input := ⟨[true], rfl, rfl⟩

private theorem branching_halts (input : List Bool) : branching.HaltsWithin input 1 := by
  intro choices hlen
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
  cases b <;> rfl

/-- Native existential acceptance must preserve an accepting branch in the presence of a
rejecting branch. This applies the constructed compiler rather than postulating a simulator. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.DecidesInSpace encBits Set.univ fun input => c * (Nat.log2 input.length + 1) :=
  finite_query_native branching 1 branching_halts fun _ =>
    ⟨fun _ => ⟨[true], rfl, rfl⟩, fun _ => trivial⟩

/-- The native compiler must also handle zero abstract steps before halting. -/
private def initiallyHalted : NondeterministicQueryMachine Unit where
  init := ()
  query _ := 0
  next _ := ()
  halted _ := true
  accept _ := true

example (input : List Bool) : initiallyHalted.Accepts input := ⟨[], rfl, rfl⟩

private theorem initiallyHalted_halts (input : List Bool) :
    initiallyHalted.HaltsWithin input 0 := by
  intro choices hlen
  have : choices = [] := List.length_eq_zero_iff.mp hlen
  subst choices
  rfl

/-- Zero abstract steps need not mean zero native instructions: the compiler still initializes
and emits the initially halted state's verdict, within a finite native all-branches clock. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.DecidesInSpace encBits Set.univ fun input => c * (Nat.log2 input.length + 1) :=
  finite_query_native initiallyHalted 0 initiallyHalted_halts fun _ =>
    ⟨fun _ => ⟨[], rfl, rfl⟩, fun _ => trivial⟩

/-- A native source that loops forever without using a work tape or emitting a bit. -/
private def loopAction : Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }

private def loopSource : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = loopAction

private theorem not_accepts_loopSource (input : List Bool) : ¬ loopSource.Accepts input := by
  have only_initial {v : FiniteCfg 0 Bool Unit}
      (h : Relation.ReflTransGen loopSource.ViewStep (loopSource.initView input) v) :
      v = loopSource.initView input := by
    induction h with
    | refl => rfl
    | @tail a b h hstep ih =>
      rw [ih] at hstep
      obtain ⟨action, ha, rfl⟩ := hstep
      change action = loopAction at ha
      subst action
      have hwork : (fun tape : Fin 0 => (Cslib.Turing.BiTape.nil : Cslib.Turing.BiTape Bool).step
          (Fin.elim0 tape)) = fun _ => Cslib.Turing.BiTape.nil :=
        funext fun tape => Fin.elim0 tape
      simpa [FiniteCfg.summarizeOutput, FiniteCfg.step, MultiTapeNTM.initView,
        FiniteCfg.init, loopAction, MultiTapeNTM.outputClass] using hwork
  intro h
  obtain ⟨v, hv, hhalt, _⟩ := MultiTapeNTM.accepts_iff_reflTransGen_viewStep.mp h
  rw [only_initial hv] at hhalt
  contradiction

/-- The first radix is closed for the looping source: it uses no work tape. -/
private theorem closed_loopSource (input : List Bool) :
    Closed loopSource (roundRadix Unit input.length 0) input := by
  rw [roundRadix_zero]
  have := card_lt_startRadix (State := Unit) input.length
  exact closed_of_runsInSpace (S := 0) (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
    (le_startRadix input.length) this (by norm_num; omega)

/-- Complement correctness applies even though the source has no halting computation. -/
example (input : List Bool) : (queryMachine loopSource).Accepts input :=
  (queryMachine_accepts_iff_not_accepts ⟨0, closed_loopSource input⟩).mpr
    (not_accepts_loopSource input)

/-- Startup counts exactly all input bits and one end marker, for arbitrary choices. -/
example (choices : List Bool) (hlen : choices.length = 4) :
    (queryMachine loopSource).run [true, false, true] choices =
      ⟨3, startRadix Unit 3, false, some (Cslib.InductiveCounting.initial
        (MultiTapeNTM.ConfigurationGraph.vertexBound (k := 0) (startRadix Unit 3))
        (MultiTapeNTM.ConfigurationGraph.startID loopSource (startRadix Unit 3)))⟩ :=
  run_bootstrap loopSource [true, false, true] choices hlen

/-- The empty input still executes its end-marker bootstrap step. -/
example : (queryMachine loopSource).run [] [false] =
    ⟨0, startRadix Unit 0, false, some (Cslib.InductiveCounting.initial
      (MultiTapeNTM.ConfigurationGraph.vertexBound (k := 0) (startRadix Unit 0))
      (MultiTapeNTM.ConfigurationGraph.startID loopSource (startRadix Unit 0)))⟩ :=
  run_bootstrap loopSource [] [false] rfl

/-- All branches, including dishonest choices, have bounded storage and a common clock. -/
example (input choices : List Bool) :
    (encRuntime ((queryMachine loopSource).run input choices)).length ≤
      storageBound 0 Unit 0 input.length :=
  length_run_le (closed_loopSource input) choices

example (input : List Bool) :
    (queryMachine loopSource).HaltsWithin input (abstractTime 0 Unit 0 input.length) :=
  queryMachine_haltsWithin (closed_loopSource input)

/-- A genuinely looping recognizer supplies the source hypotheses of the native theorem. -/
private theorem recognizes_loopSource : loopSource.RecognizesInSpace encBits ∅
    (fun input => 0 * Nat.log2 input.length + 0) := fun input =>
  ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simp [not_accepts_loopSource input]⟩

/-- The output of the actual native construction is an all-branches-halting decider. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.DecidesInSpace encBits (∅ : Set (List Bool))ᶜ
      fun input => c * (Nat.log2 input.length + 1) :=
  MultiTapeNTM.exists_decidesInSpace_compl recognizes_loopSource fun _ => le_rfl

end ComplexityTests.NLComplement
