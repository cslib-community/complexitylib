/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.AssignmentLabels
public import
  Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeEncode
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice

/-!
# Native assignment-label extraction

The explicit assignment limit pays the binary word from which each child label is sliced.
The counter, stride, requested label width and child index are also runtime binary data. Taking
and dropping prefixes cannot allocate beyond that paid word, even for malformed large widths.
The raw-bit certificate composes directly with the canonical block-label parser.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.AssignmentLabels

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.MultiTapePTM.BlockComputation.Encoding

/-- Actual binary assignment limit, counter, stride, requested width and child index. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat)))

/-- Extract a child label in native space linear in its actual encoded arguments. The binary
limit pays the source word; binary widths alone cannot allocate a list of their numeric size. -/
theorem label_inSpace : ComputableInSpace label encArgs (encList encBool)
    (fun a => (encArgs a).length) := by
  have hlimit := fst encNat (encPair encNat (encPair encNat (encPair encNat encNat)))
  have hrest := snd encNat (encPair encNat (encPair encNat (encPair encNat encNat)))
  have hcounter := hrest.fst'
  have hstride := hrest.snd'.fst'
  have hwidth := hrest.snd'.snd'.fst'
  have hchild := hrest.snd'.snd'.snd'
  have hword := budget_comp_linear NativeEncode.word_inSpace (budget_prod hlimit hcounter)
  have hstart := budget_natMul hchild hstride
  have hdrop := budget_comp_linear (listDrop encBool) (budget_prod hword hstart)
  have htake := budget_comp_linear (listTake encBool) (budget_prod hdrop hwidth)
  exact htake.of_enc_eq fun ⟨limit, counter, stride, width, child⟩ => rfl

/-- The extracted label is available as raw bits for canonical block-label checking. -/
theorem label_bits_inSpace : ComputableInSpace label encArgs encBits
    (fun a => (encArgs a).length) :=
  (budget_comp_linear (f := label) (g := fun l : List Bool => l)
    listToBits label_inSpace).of_enc_eq fun _ => rfl

end Cslib.TreeEval.Ary.Packed.AssignmentLabels
