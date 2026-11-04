/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitPathLookup

/-!
# Native classification of implicit block-tree nodes

Node replies use the existing evaluator's tags: zero for an invalid address, one for a leaf,
and two for a gate. Classification checks the actual raw path before comparing its depth to
the supplied horizon. Source padding remains a gate at internal depths.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ImplicitNode

open MultiTapeTM MultiTapeTM.ComputableInSpace Cslib.TreeEval.Ary

/-- Binary schedule/horizon metadata and an actual stored path. -/
abbrev Args := ImplicitPath.WalkArgs

/-- The evaluator's existing node-reply tag, forgetting the payload. -/
@[expose] def kind {d ℓ : ℕ} : Tree.Node d ℓ → ℕ
  | .none => 0
  | .leaf _ => 1
  | .gate _ => 2

/-- Classify a checked address without constructing its node or the unfolded tree. -/
@[expose] def classify (k : ℕ) : Args → ℕ := fun (σ, q, path) =>
  if ImplicitPath.valid k (σ, q, path) then
    if path.length = q then 1 else 2
  else 0

/-- Native classification charges the actual stored path and binary metadata. -/
theorem classify_inSpace (k : ℕ) :
    ComputableInSpace (classify k) ImplicitPath.encWalkArgs encNat
      (fun a => (ImplicitPath.encWalkArgs a).length) := by
  have hrest := snd encNat (encPair encNat (encList encNat))
  have hq := hrest.fst'
  have hlength := budget_length hrest.snd'
  have heq := budget_natEq hlength hq
  have hleaf := budget_const (encIn := ImplicitPath.encWalkArgs) (encB := encNat) 1 (.refl _)
  have hgate := budget_const (encIn := ImplicitPath.encWalkArgs) (encB := encNat) 2 (.refl _)
  have hinvalid := budget_const (encIn := ImplicitPath.encWalkArgs) (encB := encNat) 0 (.refl _)
  exact (budget_ite (ImplicitPath.valid_inSpace k) (budget_ite heq hleaf hgate)
    hinvalid).of_enc_eq fun ⟨σ, q, path⟩ => by simp only [classify, decide_eq_true_eq]

end Turing.MultiTapePTM.BlockComputation.ImplicitNode
