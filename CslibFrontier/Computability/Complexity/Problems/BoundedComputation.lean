/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Decode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Machine
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Framed bounded-computation instances

A word encodes a framed machine description, a framed input, and a most-significant-bit-first
binary clock. Total decoders interpret every word; `mk` supplies the exact canonical roundtrip.
`run` returns the bounded universal output and halted flag. A polynomial-time predicate on this
result defines a language in `E`, because the numerical clock is below `2 ^ |w|`.

The encoding API is extracted from bounded acceptance for reuse by any-output termination.

## Main definitions

* `Cslib.Complexity.BoundedComputation.mk`: frame a description, input and binary clock.
* `Cslib.Complexity.BoundedComputation.run`: interpret the decoded bounded computation.
* `Cslib.Complexity.BoundedComputation.cappedRun`: run with a unary numerical cap.

## Main results

* `Cslib.Complexity.BoundedComputation.run_mk`: canonical-triple semantics.
* `Cslib.Complexity.BoundedComputation.run_reencode`: total-decoder normalization.
* `Cslib.Complexity.BoundedComputation.computableInPolyTime_mk`: native instance construction.
* `Cslib.Complexity.BoundedComputation.setOf_run_mem_E`: polynomial-time output predicates give E.
-/

public section

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.BitString

namespace Cslib.Complexity.BoundedComputation

/-- The description field of a bit word read as an instance: the first framed word, decoded. -/
noncomputable def descOf (w : List Bool) : Desc := decodeDesc (unframe w)

/-- The input field of a bit word read as an instance: the second framed word. -/
def inputOf (w : List Bool) : List Bool := unframe (dropFrame w)

/-- The step bound field of a bit word read as an instance, in binary: the rest after the two
framed words. -/
def clockOf (w : List Bool) : List Bool := dropFrame (dropFrame w)

/-- Frame a description and input, followed by a most-significant-bit-first binary clock. -/
def mk (d : Desc) (x c : List Bool) : List Bool := frame (eDesc d) ++ (frame x ++ c)

@[simp]
theorem descOf_mk (d : Desc) (x c : List Bool) : descOf (mk d x c) = d :=
  decodeDesc_unframe_frame_append d _

@[simp]
theorem inputOf_mk (d : Desc) (x c : List Bool) : inputOf (mk d x c) = x := by
  rw [inputOf, mk, dropFrame_frame_append, unframe_frame_append]

@[simp]
theorem clockOf_mk (d : Desc) (x c : List Bool) : clockOf (mk d x c) = c := by
  rw [clockOf, mk, dropFrame_frame_append, dropFrame_frame_append]

/-- The step bound written in an instance is below `2 ^ n` for an instance of length `n`. -/
theorem binaryValue_clockOf_lt (w : List Bool) : binaryValue (clockOf w) < 2 ^ w.length :=
  (binaryValue_lt_two_pow _).trans_le (Nat.pow_le_pow_right (by norm_num)
    ((length_dropFrame_le _).trans (length_dropFrame_le _)))

/-- Run the decoded machine for the decoded binary clock, returning output and halted flag. -/
noncomputable def run (w : List Bool) : List ℕ × Bool :=
  universal (descOf w, (inputOf w).map eBit, binaryValue (clockOf w))

/-- Canonical triples run with precisely their supplied description, input and binary clock. -/
theorem run_mk (d : Desc) (x c : List Bool) :
    run (mk d x c) = universal (d, x.map eBit, binaryValue c) := by
  rw [run, descOf_mk, inputOf_mk, clockOf_mk]

/-- Re-encoding the decoded fields preserves the meaning of every word, canonical or not. -/
theorem run_reencode (w : List Bool) :
    run (mk (descOf w) (inputOf w) (clockOf w)) = run w := by
  rw [run_mk, run]

/-- Constructing a framed bounded-computation instance preserves polynomial-time computation. -/
@[fun_prop] theorem computableInPolyTime_mk {α : Type} {enc : α ↪ List Bool}
    {d : α → Desc} {x c : α → List Bool}
    (hd : ComputableInPolyTime d enc eDesc) (hx : ComputableInPolyTime x enc encBits)
    (hc : ComputableInPolyTime c enc encBits) :
    ComputableInPolyTime (fun a => mk (d a) (x a) (c a)) enc encBits := by
  have hd' := hd.encoding_comp
  unfold mk
  fun_prop

/-- Cap the numerical binary clock at the supplied unary bound before universal simulation. -/
noncomputable def cappedRun (p : List Bool × ℕ) : List ℕ × Bool :=
  universal (descOf p.1, (inputOf p.1).map eBit, boundedBinaryValue p.2 (clockOf p.1))

/-- The capped simulation is polynomial-time in the word and the cap written in unary. -/
@[fun_prop] theorem computableInPolyTime_cappedRun :
    ComputableInPolyTime cappedRun (encPair encBits encUnary) eOut := by
  unfold cappedRun descOf inputOf clockOf
  fun_prop

/-- A cap above the instance clock leaves its bounded computation unchanged. -/
theorem cappedRun_eq_run (w : List Bool) (N : ℕ) (h : binaryValue (clockOf w) ≤ N) :
    cappedRun (w, N) = run w := by
  rw [cappedRun, run, boundedBinaryValue_eq, min_eq_right h]

/-- A polynomial-time predicate on a decoded bounded computation gives an `E` language. -/
theorem setOf_run_mem_E {p : List ℕ × Bool → Bool}
    (hp : ComputableInPolyTime p eOut encBool) : {w | p (run w) = true} ∈ E encBits := by
  have hc : ComputableInPolyTime (fun q => p (cappedRun q))
      (encPair encBits encUnary) encBool := by fun_prop
  convert setOf_mem_E_of_computableInPolyTime_pad hc using 1
  ext w
  change p (run w) = true ↔ p (cappedRun (w, 2 ^ w.length)) = true
  rw [cappedRun_eq_run w _ (binaryValue_clockOf_lt w).le]

end Cslib.Complexity.BoundedComputation
