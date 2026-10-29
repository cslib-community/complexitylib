/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Machine.ChoiceTable

/-!
# Finite replay of binary counting certificates

The checker uses the existing finite configuration representation and ordinary native actions.
Its validity flag is an option: invalid indices and nonzero terminal padding fail, including
for the rejecting classifier. The empty communication interface introduces no oracle resource.
The machine, its finite control, number of tapes and block width are fixed; polynomial time is
in the encoded input/certificate pair, not uniformly in a supplied machine description.

## Main definitions

* `Turing.MultiTapeCTM.Checker.indexStep`: a finite-storage occurrence or canonical padding step.
* `Turing.MultiTapeCTM.Checker.output`: finite replay followed by a genuine halting check.
* `Turing.MultiTapeCTM.Checker.checkBinary`: the binary verifier for either terminal verdict.

## Main results

* `Turing.MultiTapeCTM.Checker.output_eq_decodeCertificate`: exact native replay correspondence.
* `Turing.MultiTapeCTM.Checker.checkBinary_eq_certificateAccepts`:
  exact binary/index correspondence.
* `Turing.MultiTapeCTM.Checker.computableInPolyTime_checkBinary`: the actual checker is
  polynomial-time, using finite dispatch and a linear encoded-storage loop invariant.

## References

The finite configuration, encoding and tidy calculus retain the source credits in their modules.
Counting semantics and canonical padding are developed in `MultiTape.Counting.Certificate`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM.Checker

open MultiTapeMachine MultiTapeTM Cslib

variable {k : ℕ} {State : Type}

/-- Existing finite native storage with no communication channels. -/
abbrev Storage (k : ℕ) (State : Type) := FiniteConfig k Bool State Empty

/-- Read the ordered transition occurrences from a fixed finite local view. -/
def localActions (machine : MultiTapeCTM k Bool State)
    (view : State × Option Bool × (Fin k → Option Bool)) : List (Turing.Action k Bool State) :=
  (machine.tr view.1 view.2.1 view.2.2 Empty.elim).map Action.emptyOracleEquiv

/-- One occurrence, or a forced zero after halting; failure is distinct from rejection. -/
def indexStep (machine : MultiTapeCTM k Bool State) (finite : Storage k State) (index : ℕ) :
    Option (Storage k State) :=
  match finite.tapes.state with
  | none => if index = 0 then some finite else none
  | some state =>
    ((localActions machine
      (state, finite.tapes.inputSymbol, finite.tapes.workTapeSymbols))[index]?).map
      (fun action => finite.step action Empty.elim Empty.elim)

/-- A completed replay returns output only when it genuinely halted. -/
def finish (finite : Storage k State) : Option (List Bool) :=
  if finite.tapes.state.isNone then some finite.tapes.output else none

/-- Replay all canonical occurrence indices using finite storage. -/
def output (machine : MultiTapeCTM k Bool State) : Storage k State → List ℕ → Option (List Bool)
  | finite, [] => finish finite
  | finite, index :: rest => do
      let next ← indexStep machine finite index
      output machine next rest

/-- Finite local views give the same ordered occurrences as a represented native configuration. -/
theorem localActions_eq_actions (machine : MultiTapeCTM k Bool State)
    {finite : Storage k State} {cfg : Cfg k Bool State finite.tapes.input}
    (h : finite.tapes.Represents cfg) {state : State} (hs : finite.tapes.state = some state) :
    localActions machine (state, finite.tapes.inputSymbol, finite.tapes.workTapeSymbols) =
      machine.actions cfg := by
  simp [MultiTapeCTM.actions, ← h.state, hs, ← h.inputSymbol, ← h.workTapeSymbols, localActions]

/-- Finite-storage replay computes exactly the previously proved certificate decoder's output. -/
theorem output_eq_decodeCertificate (machine : MultiTapeCTM k Bool State)
    {finite : Storage k State} {cfg : Cfg k Bool State finite.tapes.input}
    (h : finite.tapes.Represents cfg) (indices : List ℕ) :
    output machine finite indices =
      (machine.decodeCertificate cfg indices).map (fun r => r.2.output) := by
  induction indices generalizing finite with
  | nil =>
    cases hs : finite.tapes.state <;>
      simp [output, finish, decodeCertificate, ← h.state, hs, h.output]
  | cons index rest ih =>
    cases hs : finite.tapes.state with
    | none =>
      have hhalt : cfg.Halted := h.state.symm.trans hs
      simp only [output, bind, indexStep, hs]
      by_cases hz : index = 0
      · subst index
        rw [ite_eq_left rfl, Option.bind_some, ih h,
          machine.decodeCertificate_of_halted hhalt]
        simp [machine.decodeCertificate_of_halted hhalt, List.replicate_succ]
      · simp [hz, machine.decodeCertificate_of_halted hhalt, List.replicate_succ]
    | some state =>
      have ha := localActions_eq_actions machine h hs
      simp only [output, indexStep, ha, decodeCertificate, ← h.state, hs, step?]
      cases hi : (machine.actions cfg)[index]? with
      | none => rfl
      | some action =>
        simp only [bind, Option.map_some, Option.bind_some, Option.map_map, Function.comp_def]
        exact ih (finite := finite.step action Empty.elim Empty.elim) (h.step action)

/-- The actual finite-storage transition checker is certified, including arbitrary invalid
indices. Its fixed finite dispatch table is charged by the existing finite-domain compiler. -/
@[fun_prop]
theorem computableInPolyTime_indexStep [Finite State]
    (machine : MultiTapeCTM k Bool State) :
    ComputableInPolyTime (fun p : Storage k State × ℕ => indexStep machine p.1 p.2)
      (encPair encFiniteConfig encUnary) (encOption encFiniteConfig) := by
  refine .of_tidy ?_
  classical
  let encIn := encPair (encFiniteConfig (k := k) (State := State) (Oracle := Empty)) encUnary
  have hcfg : ComputableTidilyInPolyTime (fun p : Storage k State × ℕ => p.1)
      encIn encFiniteConfig := .fst _ _
  have hindex : ComputableTidilyInPolyTime (fun p : Storage k State × ℕ => p.2)
      encIn encUnary := .snd _ _
  have hstate := ComputableTidilyInPolyTime.finiteCfg_state.comp
    (ComputableTidilyInPolyTime.finiteConfig_tapes.comp hcfg)
  unfold indexStep
  refine ComputableTidilyInPolyTime.finite_cases
    (branch := fun state p => match state with
      | none => if p.2 = 0 then some p.1 else none
      | some state =>
        ((localActions machine
          (state, p.1.tapes.inputSymbol, p.1.tapes.workTapeSymbols))[p.2]?).map
          (fun action => p.1.step action Empty.elim Empty.elim)) hstate (fun state => ?_)
  cases state with
  | none =>
    exact (hindex.decide_eq' (.const 0)).ite_decide
      ((ComputableTidilyInPolyTime.optionSome _).comp hcfg) (.const none)
  | some state =>
    have hview : ComputableTidilyInPolyTime (fun p : Storage k State × ℕ =>
        (state, p.1.tapes.inputSymbol, p.1.tapes.workTapeSymbols)) encIn
        (encPair (encFinite State)
          (encPair (encFinEnum (Option Bool)) (encFinEnum (Fin k → Option Bool)))) := by fun_prop
    have hactions : ComputableTidilyInPolyTime (fun p : Storage k State × ℕ =>
        localActions machine (state, p.1.tapes.inputSymbol, p.1.tapes.workTapeSymbols))
        encIn (encList (encFinite (Turing.Action k Bool State))) :=
      (ComputableTidilyInPolyTime.of_finite (localActions machine)).comp hview
    refine (hactions.getElem? (encA := encFinite (Turing.Action k Bool State)) hindex).finite_cases
      (branch := fun selected p => selected.map
        (fun action => p.1.step action Empty.elim Empty.elim)) (fun selected => ?_)
    cases selected with
    | none => exact .const none
    | some action =>
      exact (ComputableTidilyInPolyTime.optionSome _).comp
        ((ComputableTidilyInPolyTime.finiteConfig_step action Empty.elim Empty.elim).comp hcfg)

/-- A replay step retains the existing linear storage bound, including forced terminal padding. -/
theorem indexStep_spaceBound (machine : MultiTapeCTM k Bool State)
    {finite next : Storage k State} {inputSize steps index : ℕ}
    (h : FiniteConfig.SpaceBound inputSize steps 0 finite)
    (hnext : indexStep machine finite index = some next) :
    FiniteConfig.SpaceBound inputSize (steps + 1) 0 next := by
  unfold indexStep at hnext
  cases hs : finite.tapes.state with
  | none =>
    simp only [hs] at hnext
    split_ifs at hnext with hz
    obtain rfl := Option.some.inj hnext
    exact h.mono le_rfl (Nat.le_succ _) le_rfl
  | some state =>
    simp only [hs] at hnext
    obtain ⟨action, _, rfl⟩ := Option.map_eq_some_iff.mp hnext
    exact h.step action Empty.elim Empty.elim

/-- The checker stores unconsumed bits and either a live finite replay or a permanent failure. -/
abbrev Runtime (k : ℕ) (State : Type) := List Bool × Option (Storage k State)

/-- Consume one fixed-width block and replay its occurrence index. The saturation cap is fixed;
for a full block it equals ordinary binary decoding. -/
def binaryStep (machine : MultiTapeCTM k Bool State) (width : ℕ)
    (runtime : Runtime k State) : Runtime k State :=
  (runtime.1.drop width, do
    let finite ← runtime.2
    indexStep machine finite (BitString.boundedBinaryValue (2 ^ width) (runtime.1.take width)))

/-- Execute one binary certificate block using the certified parser and finite replay step. -/
@[fun_prop]
theorem computableInPolyTime_binaryStep [Finite State]
    (machine : MultiTapeCTM k Bool State) (width : ℕ) :
    ComputableInPolyTime (binaryStep machine width)
      (encPair encBits (encOption encFiniteConfig))
      (encPair encBits (encOption encFiniteConfig)) := by
  let encRuntime := encPair encBits (encOption
    (encFiniteConfig (k := k) (State := State) (Oracle := Empty)))
  have hbits : ComputableInPolyTime (fun r : Runtime k State => r.1)
      encRuntime encBits := .fst _ _
  have hparse : ComputableInPolyTime (fun r : Runtime k State =>
      BitString.boundedBinaryValue (2 ^ width) (r.1.take width)) encRuntime encUnary := by
    fun_prop
  have hbody : ComputableInPolyTime (fun p : Runtime k State × Storage k State =>
      indexStep machine p.2 (BitString.boundedBinaryValue (2 ^ width) (p.1.1.take width)))
      (encPair encRuntime encFiniteConfig) (encOption encFiniteConfig) :=
    (computableInPolyTime_indexStep machine).comp
      ((ComputableInPolyTime.snd _ _).prod
        (hparse.comp (ComputableInPolyTime.fst _ _)))
  have hnext := (ComputableInPolyTime.snd encBits
    (encOption encFiniteConfig)).optionElimWithInput
      (body := fun r finite => indexStep machine finite
        (BitString.boundedBinaryValue (2 ^ width) (r.1.take width)))
      (ComputableInPolyTime.const none) hbody
  convert (hbits.bitsDropWithInput (.const width)).prod hnext using 1
  funext runtime
  simp only [binaryStep]
  cases runtime.2 <;> rfl

/-- Initialize the actual checker on an input word and a binary certificate. -/
def initial (machine : MultiTapeCTM k Bool State) (p : List Bool × List Bool) : Runtime k State :=
  (p.2, some (FiniteConfig.init machine.initial p.1))

/-- The fixed-width replay loop. A short final block remains unconsumed and is rejected later. -/
def runBinary (machine : MultiTapeCTM k Bool State) (width : ℕ)
    (p : List Bool × List Bool) : Runtime k State :=
  (binaryStep machine width)^[p.2.length / width] (initial machine p)

/-- The actual replay loop is polynomial-time. Its invariant charges the input, every work tape,
output and remaining certificate; there is no assumed simulation or counting certificate. -/
@[fun_prop]
theorem computableInPolyTime_runBinary [Finite State]
    (machine : MultiTapeCTM k Bool State) (width : ℕ) :
    ComputableInPolyTime (runBinary machine width) (encPair encBits encBits)
      (encPair encBits (encOption encFiniteConfig)) := by
  refine .of_tidy ?_
  obtain ⟨c, hstorage⟩ := length_encFiniteConfig_le (k := k) (State := State) (Oracle := Empty)
  have hcount : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => p.2.length / width)
      (encPair encBits encBits) encUnary := by fun_prop
  have hinit : ComputableTidilyInPolyTime (initial machine) (encPair encBits encBits)
      (encPair encBits (encOption encFiniteConfig)) := by unfold initial; fun_prop
  apply (ComputableTidilyInPolyTime.iterate_spec hcount hinit
    (computableInPolyTime_binaryStep machine width).tidy
    (fun p i r => r.1.length ≤ p.2.length ∧
      ∀ finite, r.2 = some finite → FiniteConfig.SpaceBound p.1.length i 0 finite)
    (fun p => ⟨le_rfl, fun finite hf => by
      obtain rfl := Option.some.inj hf
      exact FiniteConfig.spaceBound_init machine.initial p.1 0⟩) ?_
    (size := fun p => (2 * c + 2) * ((encPair encBits encBits p).length + 1))
    ((PolyBounded.const _).mul (PolyBounded.self.add (PolyBounded.const 1))) ?_).1
  · intro p i r _ hr
    refine ⟨?_, ?_⟩
    · simpa only [binaryStep, List.length_drop] using (Nat.sub_le r.1.length width).trans hr.1
    · intro next hnext
      obtain ⟨finite, hfinite, hstep⟩ := Option.bind_eq_some_iff.mp hnext
      exact indexStep_spaceBound machine (hr.2 finite hfinite) hstep
  · intro p i r hi hr
    have hi' := hi.trans (Nat.div_le_self _ _)
    have hinput := length_le_encPair_left encBits encBits p
    have hword := length_le_encPair_right encBits encBits p
    simp only [encBits_apply] at hinput hword
    cases hs : r.2 with
    | none =>
      simp only [length_encPair, encBits_apply, hs, encOption_none, List.length_nil]
      nlinarith [hr.1]
    | some finite =>
      have hfinite := hstorage p.1.length i 0 finite (hr.2 finite hs)
      simp only [length_encPair, encBits_apply, hs, encOption_some, List.length_cons]
      nlinarith [hr.1]

/-- Read the final output only after an actual simulated halt. -/
@[fun_prop]
theorem computableInPolyTime_finish [Finite State] :
    ComputableInPolyTime (finish (k := k) (State := State))
      encFiniteConfig (encOption encBits) := by
  refine .of_tidy ?_
  have hstate := ComputableTidilyInPolyTime.finiteCfg_state.comp
    (ComputableTidilyInPolyTime.finiteConfig_tapes (k := k) (State := State) (Oracle := Empty))
  have hhalt := (ComputableTidilyInPolyTime.of_finite
    (encB := encBool) (Option.isNone (α := State))).comp hstate
  have hout := ComputableTidilyInPolyTime.finiteCfg_output.comp
    (ComputableTidilyInPolyTime.finiteConfig_tapes (k := k) (State := State) (Oracle := Empty))
  exact hhalt.cond ((ComputableTidilyInPolyTime.optionSome encBits).comp hout) (.const none)

/-- A leftover partial block or an invalid/nonhalting replay has no output certificate. -/
def finishRuntime (runtime : Runtime k State) : Option (List Bool) :=
  if runtime.1 = [] then do
    let finite ← runtime.2
    finish finite
  else none

/-- On full-width certificates the actual loop is exactly the canonical index replay. Failure
remains absorbing, so the equality also covers invalid occurrence indices and padding. -/
theorem finishRuntime_iterate_binaryStep (machine : MultiTapeCTM k Bool State)
    {count width : ℕ} {word : List Bool} (h : word.length = count * width)
    (current : Option (Storage k State)) :
    finishRuntime ((binaryStep machine width)^[count] (word, current)) =
      current.bind (fun finite => output machine finite (binaryIndices count width word)) := by
  induction count generalizing word current with
  | zero =>
    have : word = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst word
    simp [finishRuntime, binaryIndices, BitString.listRows, output]
  | succ count ih =>
    have htake : (word.take width).length = width := by
      simp only [List.length_take]
      apply Nat.min_eq_left
      rw [h, Nat.succ_mul]
      exact Nat.le_add_left _ _
    have hdrop : (word.drop width).length = count * width := by
      simp only [List.length_drop, h, Nat.succ_mul, Nat.add_sub_cancel]
    have hrows := BitString.listRows_succ_append count width htake (word.drop width)
    rw [List.take_append_drop] at hrows
    have hvalue : BitString.boundedBinaryValue (2 ^ width) (word.take width) =
        BitString.binaryValue (word.take width) := by
      rw [BitString.boundedBinaryValue_eq, Nat.min_eq_right]
      exact (by simpa only [htake] using
        (BitString.binaryValue_lt_two_pow (word.take width)).le)
    rw [Function.iterate_succ_apply]
    change finishRuntime ((binaryStep machine width)^[count]
      (word.drop width, current.bind fun finite =>
        indexStep machine finite (BitString.boundedBinaryValue (2 ^ width) (word.take width)))) = _
    rw [ih hdrop]
    simp only [binaryIndices, hrows, List.map_cons, hvalue, output, bind, Option.bind_assoc]

/-- The compiled loop returns exactly the output of the canonical native decoder. The positive
block width converts the supplied binary length into the declared number of machine steps. -/
theorem finishRuntime_runBinary (machine : MultiTapeCTM k Bool State)
    {width count : ℕ} (hwidth : 0 < width) (input : List Bool) {word : List Bool}
    (hlen : word.length = count * width) :
    finishRuntime (runBinary machine width (input, word)) =
      (machine.decodeCertificate (Cfg.init machine.initial input)
        (binaryIndices count width word)).map (fun r => r.2.output) := by
  have hclock : word.length / width = count := by
    rw [hlen, Nat.mul_div_cancel _ hwidth]
  rw [runBinary, hclock, initial, finishRuntime_iterate_binaryStep machine hlen,
    Option.bind_some]
  exact output_eq_decodeCertificate machine (FiniteCfg.represents_init _ _) _

@[fun_prop]
theorem computableInPolyTime_finishRuntime [Finite State] :
    ComputableInPolyTime (finishRuntime (k := k) (State := State))
      (encPair encBits (encOption encFiniteConfig)) (encOption encBits) := by
  let encR := encPair encBits (encOption
    (encFiniteConfig (k := k) (State := State) (Oracle := Empty)))
  have hfinish : ComputableInPolyTime
      (fun p : Runtime k State × Storage k State => finish p.2)
      (encPair encR encFiniteConfig) (encOption encBits) :=
    computableInPolyTime_finish.comp (ComputableInPolyTime.snd _ _)
  have hfinal := (ComputableInPolyTime.snd encBits
    (encOption encFiniteConfig)).optionElimWithInput
    (body := fun _ finite => finish finite) (ComputableInPolyTime.const none) hfinish
  have hempty : ComputableInPolyTime (fun r : Runtime k State => decide (r.1 = []))
      encR encBool := by fun_prop
  convert hempty.ite hfinal (ComputableInPolyTime.const none) using 1
  funext runtime
  simp only [finishRuntime]
  by_cases h1 : runtime.1 = [] <;> cases runtime.2 <;> simp [h1]

/-- The actual binary checker retains validity independently of its requested terminal verdict. -/
def checkBinary (machine : MultiTapeCTM k Bool State) (width : ℕ) (verdict : Bool)
    (p : List Bool × List Bool) : Bool :=
  (finishRuntime (runBinary machine width p)).any (fun out => (out == [true]) == verdict)

/-- Each terminal verdict uses the same exact validity condition as the canonical decoder. -/
theorem checkBinary_eq_certificateAccepts (machine : MultiTapeCTM k Bool State)
    {width count : ℕ} (hwidth : 0 < width) (verdict : Bool) (input : List Bool)
    {word : List Bool} (hlen : word.length = count * width) :
    checkBinary machine width verdict (input, word) =
      machine.certificateAccepts (fun out => (out == [true]) == verdict)
        (Cfg.init machine.initial input) (binaryIndices count width word) := by
  rw [checkBinary, finishRuntime_runBinary machine hwidth input hlen]
  unfold certificateAccepts
  cases machine.decodeCertificate (Cfg.init machine.initial input)
    (binaryIndices count width word) <;> rfl

/-- Both the accepting and rejecting binary verifiers are polynomial-time on every input pair. -/
@[fun_prop]
theorem computableInPolyTime_checkBinary [Finite State]
    (machine : MultiTapeCTM k Bool State) (width : ℕ) (verdict : Bool) :
    ComputableInPolyTime (checkBinary machine width verdict) (encPair encBits encBits) encBool := by
  have hout := computableInPolyTime_finishRuntime.comp
    (computableInPolyTime_runBinary machine width)
  have hclass : ComputableInPolyTime
      (fun p : (List Bool × List Bool) × List Bool => (p.2 == [true]) == verdict)
      (encPair (encPair encBits encBits) encBits) encBool := by fun_prop
  have h := hout.optionElimWithInput (body := fun _ out => (out == [true]) == verdict)
    (ComputableInPolyTime.const false) hclass
  convert h using 1
  funext p
  simp only [checkBinary, Function.comp_def]
  cases finishRuntime (runBinary machine width p) <;> rfl

end Turing.MultiTapeCTM.Checker
