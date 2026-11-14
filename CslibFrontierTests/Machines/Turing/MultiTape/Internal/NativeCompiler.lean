/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler

/-! # Checked named native compiler construction -/

public section

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Universal

namespace CslibFrontierTests.Internal.NativeCompilerWitness

/-- A nonconstant direct compiler pipeline: preserve the input bit and attach a true tag. -/
noncomputable def tagged :
    NativeCompiler (fun b : Bool => (b, true)) encBool (encPair encBool encBool) :=
  (NativeCompiler.identity encBool).pair (NativeCompiler.const encBool encBool true)

/-- Exercise direct composition after the pair constructor. -/
noncomputable def pipeline :
    NativeCompiler (fun b : Bool => (b, true)) encBool (encPair encBool encBool) :=
  (NativeCompiler.identity (encPair encBool encBool)).comp tagged

-- Representative constructors retain actual machine terms, rather than merely existence proofs.
example : (NativeCompiler.identity encBool).machine = tidyCopy Bool :=
  rfl

example : (NativeCompiler.const encBool encBool true).machine =
    NativeCompiler.constantOutputTM (encBool true) :=
  rfl

example : (NativeCompiler.encodeFrame encBool).machine =
    Encodings.frameT.toTM.seq (rewindInput Bool) :=
  rfl

example : tagged.machine =
    appendTM
      (((NativeCompiler.encodeFrame encBool).comp
        (NativeCompiler.identity encBool)).machine)
      (NativeCompiler.const encBool encBool true).machine :=
  rfl

example : pipeline.machine =
    (NativeCompiler.identity (encPair encBool encBool)).machine.comp tagged.machine true :=
  rfl

-- State labels are composed constructively along with the machine terms.
example : (NativeCompiler.identity encBool).stateEncoding =
    NativeCompiler.sumStateEncoding NativeCompiler.unitStateEncoding
      NativeCompiler.rewindStateEncoding :=
  rfl

example : (NativeCompiler.const encBool encBool true).stateEncoding = Fin.valEmbedding :=
  rfl

example : (NativeCompiler.encodeFrame encBool).stateEncoding =
    NativeCompiler.sumStateEncoding
      (NativeCompiler.prodStateEncoding NativeCompiler.unitStateEncoding
        (NativeCompiler.prodStateEncoding
          (NativeCompiler.optionStateEncoding Turing.MultiTapeTM.Universal.eBit)
          Turing.MultiTapeTM.Universal.eBit))
      NativeCompiler.rewindStateEncoding :=
  rfl

example : tagged.stateEncoding =
    NativeCompiler.sumStateEncoding
      (((NativeCompiler.encodeFrame encBool).comp
        (NativeCompiler.identity encBool)).stateEncoding)
      (NativeCompiler.const encBool encBool true).stateEncoding :=
  rfl

example : pipeline.stateEncoding =
    NativeCompiler.sumStateEncoding
      (NativeCompiler.sumStateEncoding tagged.stateEncoding
        NativeCompiler.rewindWorkStateEncoding)
      (NativeCompiler.sumStateEncoding
        (NativeCompiler.sumStateEncoding NativeCompiler.markWorkStateEncoding
          (NativeCompiler.sumStateEncoding
            (NativeCompiler.identity (encPair encBool encBool)).stateEncoding
            NativeCompiler.markWorkStateEncoding))
        (NativeCompiler.sumStateEncoding NativeCompiler.unitStateEncoding
          NativeCompiler.rewindWorkStateEncoding)) :=
  rfl

-- The resource constants of the construction kernel remain visible definitionally.
example (b : Bool) :
    (NativeCompiler.identity encBool).time b = 2 * (encBool b).length + 4 ∧
    (NativeCompiler.identity encBool).workspace b = 0 ∧
    (NativeCompiler.const encBool encBool true).time b = (encBool true).length + 1 ∧
    (NativeCompiler.const encBool encBool true).workspace b = 0 ∧
    (NativeCompiler.encodeFrame encBool).time b = 4 * (encBool b).length + 8 ∧
    (NativeCompiler.encodeFrame encBool).workspace b = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

example (b : Bool) : tagged.time b =
    ((NativeCompiler.encodeFrame encBool).comp
        (NativeCompiler.identity encBool)).time b +
      (NativeCompiler.const encBool encBool true).time b :=
  rfl

example (b : Bool) : tagged.workspace b =
    ((NativeCompiler.encodeFrame encBool).comp
        (NativeCompiler.identity encBool)).workspace b +
      (NativeCompiler.const encBool encBool true).workspace b +
      2 * max
        ((NativeCompiler.encodeFrame encBool).comp
          (NativeCompiler.identity encBool)).tapeCount
        (NativeCompiler.const encBool encBool true).tapeCount :=
  rfl

example (b : Bool) : pipeline.time b =
    tagged.time b +
      (NativeCompiler.identity (encPair encBool encBool)).time (b, true) +
      4 * (encPair encBool encBool (b, true)).length + 9 :=
  rfl

example (b : Bool) : pipeline.workspace b =
    tagged.workspace b +
      (NativeCompiler.identity (encPair encBool encBool)).workspace (b, true) +
      5 * (encPair encBool encBool (b, true)).length +
      (6 * max tagged.tapeCount
        (NativeCompiler.identity (encPair encBool encBool)).tapeCount + 20) :=
  rfl

example : pipeline.description =
    @desc pipeline.tapeCount Bool pipeline.State pipeline.stateFintype inferInstance
      pipeline.stateEncoding eBit pipeline.machine :=
  pipeline.description_eq_desc

example : pipeline.staticBits =
    descLen (@desc pipeline.tapeCount Bool pipeline.State pipeline.stateFintype inferInstance
      pipeline.stateEncoding eBit pipeline.machine) := by
  rw [pipeline.staticBits_eq_descLen, pipeline.description_eq_desc]

example (b : Bool) : pipeline.inputBits b = (encBool b).length :=
  rfl

example (b : Bool) :
    pipeline.outputBits b = (encPair encBool encBool (b, true)).length :=
  rfl

-- Both branches compute, and the checked pipeline is genuinely nonconstant.
example : pipeline.machine.ComputesTidilyInTimeAndSpace
    (encBool false) (encPair encBool encBool (false, true))
    (pipeline.time false) (pipeline.workspace false) :=
  pipeline.computes false

example : pipeline.machine.ComputesTidilyInTimeAndSpace
    (encBool true) (encPair encBool encBool (true, true))
    (pipeline.time true) (pipeline.workspace true) :=
  pipeline.computes true

-- The forward comparison keeps the existing plain calculus as the public consumer interface.
example : ComputableInTimeAndSpace (fun b : Bool => (b, true)) encBool
    (encPair encBool encBool) pipeline.time pipeline.workspace :=
  pipeline.computableInTimeAndSpace

example : encPair encBool encBool (false, true) ≠ encPair encBool encBool (true, true) := by
  decide

end CslibFrontierTests.Internal.NativeCompilerWitness
