/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Ary.Packed.AssignmentLabelsSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProviderLabels
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi

/-!
# Native replay labels from packed assignments

The Boolean block gate has one preceding-control child followed by three providers for each
work tape. These words are sliced from the actual binary interpolation counter, padded using
its explicit loop limit. No truth table or interval-index list is constructed. The number of
children is fixed by the simulated machine; stride and label width remain runtime inputs.

Acquiring these words does not assert they are successful block labels: the checked provider
parser still validates every word, including words at unused ports.

`Args` names the four binary registers and `Words` separates the previous control label from
the provider family. Their structure encodings retain the original field order and framing.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Assignments

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib.TreeEval.Ary.Packed

/-- Explicit assignment limit, counter, padded child stride and actual label width. -/
structure Args where
  /-- Assignment limit whose binary storage pays for the padded source word. -/
  limit : ℕ
  /-- Current binary interpolation assignment. -/
  counter : ℕ
  /-- Padded number of bits between consecutive child labels. -/
  stride : ℕ
  /-- Number of bits requested from each child label. -/
  width : ℕ

/-- Binary limit, counter, stride and width, in that order; the first three fields are framed. -/
enc_structure encArgs : Args where
  limit : encNat, counter : encNat, stride : encNat, width : encNat

/-- Previous label followed by the fixed family of work-tape provider labels. -/
@[ext]
structure Words (k : ℕ) where
  /-- Label of the preceding control child. -/
  previous : List Bool
  /-- Labels indexed by work tape and then neighboring block. -/
  providers : Providers.Labels.ProviderWords k

noncomputable section

variable {k : ℕ}

/-- Framed raw previous-label bits followed by the fixed provider-family encoding. -/
enc_structure encWords : Words k where
  previous : encBits, providers : (Providers.Labels.encProviderWords (k := k))

end

/-- The first child is the preceding control; subsequent children are ordered by work tape,
then by the three neighboring blocks. -/
@[expose] def labels (k : ℕ) (a : Args) : Words k where
  previous := AssignmentLabels.label (a.limit, a.counter, a.stride, a.width, 0)
  providers h δ :=
    AssignmentLabels.label (a.limit, a.counter, a.stride, a.width, 1 + 3 * h.val + δ.val)

/-- Label acquisition is native and linear in the actual binary assignment storage. The
constant depends only on the fixed number of simulated work tapes. -/
theorem labels_inSpace (k : ℕ) :
    ComputableInSpace (labels k) encArgs encWords (fun a => (encArgs a).length) := by
  have hlimit := of_inO encArgs_limit_inO
  have hcounter := of_inO encArgs_counter_inO
  have hstride := of_inO encArgs_stride_inO
  have hwidth := of_inO encArgs_width_inO
  have hlabel (child : ℕ) := budget_comp_linear AssignmentLabels.label_bits_inSpace
    (budget_prod hlimit (budget_prod hcounter (budget_prod hstride
      (budget_prod hwidth (budget_const (encB := encNat) child (.refl _))))))
  have hproviders := pi_linear fun h : Fin k => pi_linear fun δ : Fin 3 =>
    hlabel (1 + 3 * h.val + δ.val)
  exact encWords_mk_budget (hlabel 0) hproviders

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Assignments
