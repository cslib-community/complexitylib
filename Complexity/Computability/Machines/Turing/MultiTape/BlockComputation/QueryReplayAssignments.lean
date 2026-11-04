/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.AssignmentLabelsSpace
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProviderLabels
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi

/-!
# Native replay labels from packed assignments

The Boolean block gate has one preceding-control child followed by three providers for each
work tape. These words are sliced from the actual binary interpolation counter, padded using
its explicit loop limit. No truth table or interval-index list is constructed. The number of
children is fixed by the simulated machine; stride and label width remain runtime inputs.

Acquiring these words does not assert they are successful block labels: the checked provider
parser still validates every word, including words at unused ports.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Assignments

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib.TreeEval.Ary.Packed

/-- Explicit assignment limit, counter, padded child stride and actual label width. -/
abbrev Args := ℕ × ℕ × ℕ × ℕ

/-- Every binary assignment register is charged by its actual encoding. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))

/-- Previous label followed by the fixed family of work-tape provider labels. -/
abbrev Words (k : ℕ) := List Bool × Providers.Labels.ProviderWords k

/-- Actual extracted words, in the checked provider parser's encoding. -/
@[expose] noncomputable def encWords (k : ℕ) : Words k ↪ List Bool :=
  encPair encBits Providers.Labels.encProviderWords

/-- The first child is the preceding control; subsequent children are ordered by work tape,
then by the three neighboring blocks. -/
@[expose] def labels (k : ℕ) : Args → Words k := fun (limit, counter, stride, width) =>
  (AssignmentLabels.label (limit, counter, stride, width, 0), fun h δ =>
    AssignmentLabels.label (limit, counter, stride, width, 1 + 3 * h.val + δ.val))

/-- Label acquisition is native and linear in the actual binary assignment storage. The
constant depends only on the fixed number of simulated work tapes. -/
theorem labels_inSpace (k : ℕ) :
    ComputableInSpace (labels k) encArgs (encWords k) (fun a => (encArgs a).length) := by
  have hlimit := fst encNat (encPair encNat (encPair encNat encNat))
  have hrest := snd encNat (encPair encNat (encPair encNat encNat))
  have hcounter := hrest.fst'
  have hstride := hrest.snd'.fst'
  have hwidth := hrest.snd'.snd'
  have hlabel (child : ℕ) := budget_comp_linear AssignmentLabels.label_bits_inSpace
    (budget_prod hlimit (budget_prod hcounter (budget_prod hstride
      (budget_prod hwidth (budget_const (encB := encNat) child (.refl _))))))
  have hproviders := pi_linear fun h : Fin k => pi_linear fun δ : Fin 3 =>
    hlabel (1 + 3 * h.val + δ.val)
  exact budget_prod (hlabel 0) hproviders

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Assignments
