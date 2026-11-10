/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.ChoiceTable
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Decode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Padding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Tactic.OptionMatch

/-!
# Views and their codes in polynomial time

The step relation of the views of a machine with finitely many states
(`Turing.MultiTapeNTM.ViewStep`) is decided by `Turing.MultiTapeNTM.viewStepB`: a halted view
steps only to itself, and a running view to the summarized result of one of the finitely many
actions its transition relation permits for its control and read symbols. The test is
polynomial-time in the encoded pair of views: it branches on the finite key of the first view,
and each branch compares the second view with the results of a fixed finite list of fixed actions.

For Savitch's theorem the views are written as words of one width: the code of a view is a zero
tag followed by its encoding padded by `Cslib.BitString.padWord`, and the accepting code is the
word of all ones. The edge test `Turing.MultiTapeNTM.codeEdge` decodes both words by
`Turing.MultiTapeTM.decodeFiniteCfg` and links the code of a view to the code of each view it
steps to, and the code of a halted view with output `[true]` to every word with tag one. Malformed
words with tag zero decode to some view, which is harmless: every word with tag zero reachable
from the code of the initial view decodes to a view reachable from the initial view. Acceptance
is then reachability of the accepting code
(`Turing.MultiTapeNTM.accepts_iff_reflTransGen_codeStep`), and the edge test, the initial code and
the accepting code are polynomial-time.

## Main definitions

* `Turing.MultiTapeNTM.viewStepB`: the Boolean step test of views.
* `Turing.MultiTapeNTM.viewCode`, `Turing.MultiTapeNTM.acceptCode`: codes of views and the
  accepting code.
* `Turing.MultiTapeNTM.codeEdge`, `Turing.MultiTapeNTM.CodeStep`: the edges between codes.

## Main results

* `Turing.MultiTapeNTM.viewStepB_iff`: the test decides `Turing.MultiTapeNTM.ViewStep`.
* `Turing.MultiTapeNTM.computableInPolyTime_viewStepB`: the test is polynomial-time.
* `Turing.MultiTapeNTM.computableInPolyTime_decodeView`: reading the view of a computed code is
  polynomial-time.
* `Turing.MultiTapeNTM.accepts_iff_reflTransGen_codeStep`: acceptance is reachability of the
  accepting code.
* `Turing.MultiTapeNTM.computableInPolyTime_codeEdge`,
  `Turing.MultiTapeNTM.computableInPolyTime_viewCode_initView`,
  `Turing.MultiTapeNTM.computableInPolyTime_acceptCode`: the edge test, the initial code and the
  accepting code are polynomial-time.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
-/

@[expose] public section

namespace Turing

open MultiTapeTM

namespace MultiTapeTM.ComputableInPolyTime

/-- The output summary is polynomial-time on raw words. -/
@[fun_prop]
theorem outputClass :
    ComputableInPolyTime MultiTapeNTM.outputClass encBits encBits := by
  have h : MultiTapeNTM.outputClass = fun word : List Bool =>
      if decide (word = []) then [] else if decide (word = [true]) then [true] else [false] := by
    funext word
    unfold MultiTapeNTM.outputClass
    split_ifs <;> simp_all
  rw [h]
  exact ite' (decide_eq' id' (const [])) (const [])
    (ite' (decide_eq' id' (const [true])) (const [true]) (const [false]))

/-- Summarizing the output of a configuration is polynomial-time. -/
@[fun_prop]
theorem finiteCfg_summarizeOutput {k : ℕ} {State : Type} [Finite State] :
    ComputableInPolyTime (FiniteCfg.summarizeOutput (k := k) (State := State)) encFiniteCfg
      encFiniteCfg :=
  finiteCfg_mk finiteCfg_input finiteCfg_state finiteCfg_inputPos finiteCfg_workTapes
    (outputClass.comp finiteCfg_output)

end MultiTapeTM.ComputableInPolyTime

namespace MultiTapeNTM

variable {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)

open scoped Classical in
/-- **The step test of views.** -/
noncomputable def viewStepB (views : FiniteCfg k Bool State × FiniteCfg k Bool State) : Bool :=
  match views.1.state with
  | none => decide (views.2 = views.1)
  | some state => (ntm.actions state views.1.inputSymbol views.1.workTapeSymbols).any
      fun action => decide (views.2 = (views.1.step action).summarizeOutput)

/-- The test decides the steps of views. -/
theorem viewStepB_iff {finite next : FiniteCfg k Bool State} :
    ntm.viewStepB (finite, next) = true ↔ ntm.ViewStep finite next := by
  unfold viewStepB ViewStep
  rcases finite.state with _ | state
  · simp
  · simp only [List.any_eq_true, decide_eq_true_eq, mem_actions]

/-- **The step test is polynomial-time** in the encoded pair of views. -/
theorem computableInPolyTime_viewStepB :
    ComputableInPolyTime ntm.viewStepB (encPair encFiniteCfg encFiniteCfg) encBool := by
  classical
  -- branch on the finite key of the first view
  let key (views : FiniteCfg k Bool State × FiniteCfg k Bool State) :
      Option State × Option Bool × (Fin k → Option Bool) :=
    (views.1.state, views.1.inputSymbol, views.1.workTapeSymbols)
  let branch (tag : Option State × Option Bool × (Fin k → Option Bool))
      (views : FiniteCfg k Bool State × FiniteCfg k Bool State) : Bool :=
    match tag.1 with
    | none => decide (views.2 = views.1)
    | some state => (ntm.actions state tag.2.1 tag.2.2).any
        fun action => decide (views.2 = (views.1.step action).summarizeOutput)
  have heq : ntm.viewStepB = fun views => branch (key views) views := by
    funext views
    rfl
  have hfst := ComputableInPolyTime.fst (encFiniteCfg (k := k) (State := State))
    (encFiniteCfg (k := k) (State := State))
  have hsnd := ComputableInPolyTime.snd (encFiniteCfg (k := k) (State := State))
    (encFiniteCfg (k := k) (State := State))
  rw [heq]
  refine ComputableInPolyTime.finite_cases
    (tagEncoding := encPair (encFinite _) (encPair (encFinEnum _) (encFinEnum _))) ?_ fun tag => ?_
  · exact (ComputableInPolyTime.finiteCfg_state.comp hfst).prod
      ((ComputableInPolyTime.finiteCfg_inputSymbol.comp hfst).prod
        (ComputableInPolyTime.finiteCfg_workTapeSymbols.comp hfst))
  · rcases tag with ⟨_ | state, symbol, work⟩
    · exact ComputableInPolyTime.decide_eq' hsnd hfst
    · -- a fixed finite list of actions, each compared by its own certificate
      dsimp only [branch]
      induction ntm.actions state symbol work with
      | nil => exact ComputableInPolyTime.const false
      | cons action actions ih =>
        simp only [List.any_cons]
        exact ComputableInPolyTime.bool_or.comp ((ComputableInPolyTime.decide_eq' hsnd
          ((ComputableInPolyTime.finiteCfg_summarizeOutput.comp
            (ComputableInPolyTime.finiteCfg_step action)).comp hfst)).prod ih)

/-! ### Codes of views -/

/-- The code of a view for encodings of length at most `width`: a zero tag, then its encoding
padded to `2 * width + 1` bits (`Cslib.BitString.padWord`). -/
noncomputable def viewCode (width : ℕ) (finite : FiniteCfg k Bool State) : List Bool :=
  false :: Cslib.BitString.padWord width (encFiniteCfg finite)

/-- The accepting code for width `width`: all ones. Its tag is one, so it is no view's code. -/
def acceptCode (width : ℕ) : List Bool := List.replicate (2 * width + 2) true

/-- Read the view of a code with a zero tag: decode its first frame by
`Turing.MultiTapeTM.decodeFiniteCfg`. -/
noncomputable def decodeView : List Bool → Option (FiniteCfg k Bool State)
  | false :: code => some (decodeFiniteCfg (unframe code))
  | _ => none

open scoped Classical in
/-- **The edge test of codes.** A code of a view `finite` has an edge to every code with tag one
if `finite` has halted with output `[true]`, and to the code of every view `finite` steps to. -/
noncomputable def codeEdge (code next : List Bool) : Bool :=
  match decodeView code with
  | none => false
  | some finite =>
    if next.headD false then decide (finite.state = none) && decide (finite.output = [true])
    else match decodeView next with
      | none => false
      | some next => ntm.viewStepB (finite, next)

/-- The edges between codes of `2 * width + 2` bits. -/
def CodeStep (width : ℕ) (code next : List Bool) : Prop :=
  code.length = 2 * width + 2 ∧ next.length = 2 * width + 2 ∧ ntm.codeEdge code next = true

variable {ntm}

/-- The code of a view decodes to the view. -/
theorem decodeView_viewCode (width : ℕ) (finite : FiniteCfg k Bool State) :
    decodeView (viewCode width finite) = some finite := by
  simp only [decodeView, viewCode, Cslib.BitString.padWord, unframe_frame_append,
    decodeFiniteCfg_encFiniteCfg]

/-- The code of a view with an encoding of length at most `width` has `2 * width + 2` bits. -/
theorem length_viewCode {width : ℕ} {finite : FiniteCfg k Bool State}
    (h : (encFiniteCfg finite).length ≤ width) :
    (viewCode width finite).length = 2 * width + 2 := by
  rw [viewCode, List.length_cons, Cslib.BitString.length_padWord h]

/-- Between codes of views, the edges are the steps of the views. -/
theorem codeEdge_viewCode {width : ℕ} {finite next : FiniteCfg k Bool State} :
    ntm.codeEdge (viewCode width finite) (viewCode width next) = true ↔
      ntm.ViewStep finite next := by
  simp only [codeEdge, viewCode, decodeView, Cslib.BitString.padWord, unframe_frame_append,
    decodeFiniteCfg_encFiniteCfg]
  exact ntm.viewStepB_iff

/-- The code of a view has an edge to the accepting code exactly when the view has halted with
output `[true]`. -/
theorem codeEdge_acceptCode {width : ℕ} {finite : FiniteCfg k Bool State} :
    ntm.codeEdge (viewCode width finite) (acceptCode width) = true ↔
      finite.state = none ∧ finite.output = [true] := by
  simp only [codeEdge, decodeView_viewCode, acceptCode, List.replicate_succ, List.headD_cons,
    ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]

/-- **Acceptance is reachability of the accepting code**, along the edges between codes of a
width at least the length of the encoding of every reachable view. -/
theorem accepts_iff_reflTransGen_codeStep {input : List Bool} {width : ℕ}
    (hwidth : ∀ finite, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite →
      (encFiniteCfg finite).length ≤ width) :
    ntm.Accepts input ↔ Relation.ReflTransGen (ntm.CodeStep width)
      (viewCode width (ntm.initView input)) (acceptCode width) := by
  rw [accepts_iff_reflTransGen_viewStep]
  constructor
  · rintro ⟨finite, hreach, hstate, houtput⟩
    have hcodes : ∀ next, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) next →
        Relation.ReflTransGen (ntm.CodeStep width) (viewCode width (ntm.initView input))
          (viewCode width next) := by
      intro next hnext
      induction hnext with
      | refl => rfl
      | @tail view next hview hstep ih =>
        exact ih.tail ⟨length_viewCode (hwidth _ hview),
          length_viewCode (hwidth _ (hview.tail hstep)), (codeEdge_viewCode).mpr hstep⟩
    exact (hcodes finite hreach).tail ⟨length_viewCode (hwidth _ hreach),
      List.length_replicate .., (codeEdge_acceptCode).mpr ⟨hstate, houtput⟩⟩
  · intro hreach
    -- every reachable code decodes to a reachable view, or has tag one after an accepting view
    have hinv : ∀ code, Relation.ReflTransGen (ntm.CodeStep width)
        (viewCode width (ntm.initView input)) code →
        (∃ finite, decodeView code = some finite ∧
          Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite) ∨
        (code.head? = some true ∧ ∃ finite,
          Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite ∧
            finite.state = none ∧ finite.output = [true]) := by
      intro code hcode
      induction hcode with
      | refl => exact .inl ⟨_, decodeView_viewCode _ _, .refl⟩
      | @tail code next _ hstep ih =>
        obtain ⟨-, -, hedge⟩ := hstep
        unfold codeEdge at hedge
        rcases ih with ⟨finite, hfinite, hreach⟩ | ⟨hhead, -⟩
        · rw [hfinite] at hedge
          rcases next with _ | ⟨_ | _, next⟩
          · simp [decodeView] at hedge
          · simp only [List.headD_cons, Bool.false_eq_true, ↓reduceIte] at hedge
            rcases hview : decodeView (false :: next) with _ | view
            · simp [hview] at hedge
            · simp only [hview, viewStepB_iff] at hedge
              exact .inl ⟨view, rfl, hreach.tail hedge⟩
          · simp only [List.headD_cons, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hedge
            exact .inr ⟨rfl, finite, hreach, hedge⟩
        · rcases code with _ | ⟨_ | _, code⟩
          · simp at hhead
          · simp at hhead
          · simp [decodeView] at hedge
    rcases hinv _ hreach with ⟨finite, hfinite, -⟩ | ⟨-, hacc⟩
    · simp [acceptCode, List.replicate_succ, decodeView] at hfinite
    · exact hacc

/-! ### The edge test in polynomial time -/

/-- Reading the view of a code, by cases on its tag. -/
theorem decodeView_eq (code : List Bool) :
    decodeView code = if code.headD true then none else
      some (decodeFiniteCfg (k := k) (State := State) (unframe code.tail)) := by
  rcases code with _ | ⟨_ | _, code⟩ <;> rfl

section Certificate

variable {α : Type} {encA : α ↪ List Bool}

/-- Reading the view of a computed code is polynomial-time. -/
theorem computableInPolyTime_decodeView {code : α → List Bool}
    (hcode : ComputableInPolyTime code encA encBits) :
    ComputableInPolyTime (fun a => decodeView (k := k) (State := State) (code a)) encA
      (encOption encFiniteCfg) := by
  simp only [decodeView_eq]
  exact ComputableInPolyTime.ite' ((ComputableInPolyTime.headD (encA := encBool) true).comp hcode)
    (.const none)
    ((ComputableInPolyTime.optionSome _).comp
      (ComputableInPolyTime.decodeFiniteCfg.comp (ComputableInPolyTime.unframe.comp
      ((ComputableInPolyTime.tail (encA := encBool)).comp hcode))))

/-- **The edge test of codes is polynomial-time.** -/
theorem computableInPolyTime_codeEdge
    {code next : α → List Bool} (hcode : ComputableInPolyTime code encA encBits)
    (hnext : ComputableInPolyTime next encA encBits) :
    ComputableInPolyTime (fun a => ntm.codeEdge (code a) (next a)) encA encBool := by
  classical
  unfold codeEdge
  option_match_to_elim
  have hfst := ComputableInPolyTime.fst encA (encFiniteCfg (k := k) (State := State))
  have hsnd := ComputableInPolyTime.snd encA (encFiniteCfg (k := k) (State := State))
  refine (computableInPolyTime_decodeView hcode).optionElimWithInput (.const false) ?_
  refine ComputableInPolyTime.ite'
    ((ComputableInPolyTime.headD (encA := encBool) false).comp (hnext.comp hfst)) ?_ ?_
  · exact ComputableInPolyTime.bool_and.comp
      (((ComputableInPolyTime.of_finite fun state : Option State =>
          decide (state = none)).comp (ComputableInPolyTime.finiteCfg_state.comp hsnd)).prod
      (ComputableInPolyTime.decide_eq'
        (ComputableInPolyTime.finiteCfg_output.comp hsnd) (.const [true])))
  · refine (computableInPolyTime_decodeView (hnext.comp hfst)).optionElimWithInput
      (.const false) ?_
    exact ntm.computableInPolyTime_viewStepB.comp
      ((hsnd.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))

/-- The code of the initial view of a computed input is polynomial-time, for a polynomial-time
width. -/
theorem computableInPolyTime_viewCode_initView {width : α → ℕ} {word : α → List Bool}
    (hwidth : ComputableInPolyTime width encA encUnary)
    (hword : ComputableInPolyTime word encA encBits) :
    ComputableInPolyTime (fun a => viewCode (width a) (ntm.initView (word a))) encA encBits := by
  have hinit := ComputableInPolyTime.finiteCfg_init (k := k) hword ntm.q₀
  exact ComputableInPolyTime.bitsAppend (left := fun _ => [false]) (.const _)
    (ComputableInPolyTime.bitsPadWord hwidth (hinit.of_enc_eq fun _ => rfl))

/-- The accepting code of a polynomial-time width is polynomial-time. -/
theorem computableInPolyTime_acceptCode {width : α → ℕ}
    (hwidth : ComputableInPolyTime width encA encUnary) :
    ComputableInPolyTime (fun a => acceptCode (width a)) encA encBits :=
  (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2) hwidth)
      (.const 2))

end Certificate

end MultiTapeNTM

end Turing
