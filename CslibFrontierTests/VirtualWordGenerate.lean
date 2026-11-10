/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeGenerate

/-!
# Live frame generation and native consumption

One fixed program computes its cut from the first input bit, negates that bit for its suffix,
and retains the original read-only word as the tail. The consumer frames the resulting virtual
word. Empty, false-headed and true-headed inputs exercise distinct prefix/suffix combinations.
-/

public section

namespace Cslib.Complexity.VirtualWordGenerateTest

open Turing Turing.MultiTapeTM VirtualWord

/-- A runtime cut computed from a live input bit, with zero on empty input. -/
@[expose] def cut (x : List Bool) : ℕ := (x.headD false).toNat

/-- A changing suffix computed by an actual transducer, rather than supplied as an oracle. -/
@[expose] def suffix (x : List Bool) : List Bool := (x.take 1).map not

/-- Both the cut and address vary with the first input bit; both have binary encodings. -/
@[expose] def data (x : List Bool) : Data := (cut x, suffix x, cut x)

/-- The cut is always a valid prefix, including empty input. -/
theorem cut_le (x : List Bool) : cut x ≤ x.length := by
  cases x with
  | nil => decide
  | cons b xs => cases b <;> simp [cut]

/-- Actual component programs construct the small header. -/
theorem data_logSpace : ComputableInLogSpace data encBits encData := by
  have hh := ComputableInLogSpace.bitsHeadD false
  have hc : ComputableInLogSpace cut encBits encNat :=
    (ComputableInLogSpace.of_finite (encIn := encBool) Bool.toNat).comp hh
  have hs : ComputableInLogSpace suffix encBits encBits :=
    (ComputableInLogSpace.bitsMap not).comp
      (ComputableInLogSpace.of_take_one (encIn := encBits) (encOut := encBits)
        (f := fun x => x.take 1) fun _ => rfl)
  exact hc.pair (hs.pair hc)

/-- This certificate runs the generator; its output is precisely the bytes loaded by the
runtime consumer. The original input is emitted as the tail, never saved as workspace. -/
theorem generated_frame : ComputableInLogSpace (Generate.prepare _root_.id data cut_le)
    encBits Simulation.encInput :=
  Generate.prepare_logSpace ComputableInLogSpace.id data_logSpace cut_le

/-- Run a nonconstant live query generator, discard its prefix through the existing counter
program and generate a runtime frame. The query stream is recomputed, not stored. -/
theorem query_frame : ComputableInLogSpace
    (Generate.prepare _root_.id
      (fun x => (cut x, (x.map not).drop (cut x), cut x)) cut_le)
    encBits Simulation.encInput := by
  have hh := ComputableInLogSpace.bitsHeadD false
  have hc := (ComputableInLogSpace.of_finite (encIn := encBool)
    (encMid := encUnary) Bool.toNat).comp hh
  have hi := (ComputableInLogSpace.of_finite (encIn := encBool)
    (encMid := encNat) Bool.toNat).comp hh
  exact Generate.prepare_logSpace ComputableInLogSpace.id
    (localQueryData_logSpace (ComputableInLogSpace.bitsMap not) hc hi) cut_le

/-- A single native composed program generates the variable header and consumes the virtual
word through recomputation. The bound is logarithmic in the original raw input length. -/
theorem generated_consumer : ComputableInLogSpace
    (fun x => frame (word x (cut x) (suffix x))) encBits encBits := by
  apply Generate.consume ComputableInLogSpace.id data_logSpace cut_le
    (ComputableInLogSpace.of_frame (encIn := encBits) (encOut := encBits)
      (f := frame) fun _ => rfl) 16 2 1
  · intro x
    have hs : (suffix x).length ≤ 1 := by simp [suffix]
    have hc : (encNat (cut x)).length ≤ 1 := by
      cases x with
      | nil => decide
      | cons b xs => cases b <;> norm_num [cut, encNat_apply]
    simp only [data, encData, length_encPair, encBits_apply]
    nlinarith
  · intro x
    change (word x (cut x) (suffix x)).length ≤ _
    rw [length_word _ _ _ (cut_le x)]
    have hs : (suffix x).length ≤ 1 := by simp [suffix]
    simp only [encBits_apply, pow_one]
    have := cut_le x
    omega

/-- A satisfiable local-query instance: the first bit is retained and the last bit strictly
falls. The caller encoding is the ordinary pair encoding, with no artificial padding. -/
theorem local_client : ComputableInLogSpace
    (fun p : Bool × Bool => frame [p.1, false]) (encPair encBool encBool) encBits := by
  apply consume_localQuery
    (x := fun p : Bool × Bool => [p.1, true]) (cut := fun _ => 1)
    (ComputableInLogSpace.of_finite _) (ComputableInLogSpace.of_finite _)
    (ComputableInLogSpace.const _) (fun _ => by change 1 = 2 - Nat.clog 2 2; decide) ?_ ?_
    (ComputableInLogSpace.of_frame (encIn := encBits) (encOut := encBits)
      (f := frame) fun _ => rfl)
  · intro p
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> decide
  · intro p
    simp

-- Both prefix and suffix change; the answer is not a constant consumer.
example : word [false, true, true] (cut [false, true, true]) (suffix [false, true, true]) =
    [true] := rfl
example : word [true, false, true] (cut [true, false, true]) (suffix [true, false, true]) =
    [true, false] := rfl
example : frame (word [] (cut []) (suffix [])) = [false] := rfl
example : frame (word [false] (cut [false]) (suffix [false])) = [true, true, false] := rfl
example : frame (word [true] (cut [true]) (suffix [true])) =
    [true, true, true, false, false] := rfl

example : (List.map not [true, false, true]).drop (cut [true, false, true]) =
    [true, false] := rfl
example : (List.map not [false, false, true]).drop (cut [false, false, true]) =
    [true, true, false] := rfl

-- Header decoding recovers the generated variable parameters, and its tail is unchanged.
example (x : List Bool) : Runtime.decode (unframe
    (Simulation.encInput (Generate.prepare _root_.id data cut_le x))) = data x := by
  change Runtime.decode (unframe (frame (encData (data x)) ++ x)) = data x
  rw [unframe_frame_append, Runtime.decode_encData]
example (x : List Bool) : dropFrame
    (Simulation.encInput (Generate.prepare _root_.id data cut_le x)) = x := by
  change dropFrame (frame (encData (data x)) ++ x) = x
  rw [dropFrame_frame_append]

end Cslib.Complexity.VirtualWordGenerateTest
