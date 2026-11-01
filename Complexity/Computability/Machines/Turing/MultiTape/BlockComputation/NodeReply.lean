/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitNode
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialVector
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerNative

/-!
# Native node replies for the implicit block evaluator

Node replies use the evaluator's existing tags: invalid zero, leaf one and gate two. A leaf
returns its packed source vector only when actual assignment-capacity storage pays its runtime
length. Gates return only a tag; gate interpolation is a separate supplier operation.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.NodeReply

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- Actual path metadata and the paid source-vector parameters. -/
abbrev Args := ImplicitPath.WalkArgs × InitialVector.Args

/-- The raw path, schedule and all binary capacity/packing data are charged explicitly. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair ImplicitPath.encWalkArgs InitialVector.encArgs

/-- Produce exactly the raw evaluator's node-reply format, rejecting unpaid leaf vectors. -/
@[expose] def reply (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) : Args → RawController.Reply :=
  fun (address, (limit, m, r)) =>
    let tag := ImplicitNode.classify k address
    if tag = 1 then
      if r ≤ limit.size then (1, InitialVector.values M e (limit, m, r)) else (0, [])
    else (tag, [])

/-- Classification and paid leaf construction are native in actual encoded-argument space. -/
theorem reply_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (reply M e) encArgs RawController.encReply
      (fun a => (encArgs a).length) := by
  have ha := fst ImplicitPath.encWalkArgs InitialVector.encArgs
  have hv := snd ImplicitPath.encWalkArgs InitialVector.encArgs
  have htag := budget_comp_linear (ImplicitNode.classify_inSpace k) ha
  have hleaf := budget_natEq htag (budget_const (encB := encNat) 1 (.refl _))
  have hlimit := hv.fst'
  have hr := hv.snd'.snd'
  have hsize := budget_comp_linear natSize hlimit
  have hcapacity := budget_finite (encC := encBool) Bool.not (budget_natLt hsize hr)
  have hvalues := budget_comp_linear (InitialVector.values_inSpace M e) hv
  have hempty := budget_const (encIn := encArgs) (encB := encList encNat) [] (.refl _)
  have hsuccess := budget_prod (budget_const (encB := encNat) 1 (.refl _)) hvalues
  have hfailure := budget_prod (budget_const (encB := encNat) 0 (.refl _)) hempty
  have hother := budget_prod htag hempty
  refine (budget_ite hleaf (budget_ite hcapacity hsuccess hfailure) hother).of_enc_eq ?_
  rintro ⟨address, limit, m, r⟩
  by_cases hc : r ≤ limit.size
  · have hn : ¬limit.size < r := by omega
    simp [reply, hc, hn]
  · have hn : limit.size < r := by omega
    simp [reply, hc, hn]

end Turing.MultiTapePTM.BlockComputation.NodeReply
