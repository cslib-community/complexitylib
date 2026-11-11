/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Unsigned certificate counts for oracle replay

Each instruction-indexed transcript receives the product of its oracle certificate counts.
A query contributes the count supporting its guessed answer; a local or halted instruction
contributes `1` for the canonical padding bit `false` and `0` for `true`. Positive path counts
therefore characterize the canonical oracle transcript, and counts bounded by one preserve
unambiguity. These are the common certificates used by the decision and counting lowness proofs.

## Main definitions

* `replayPathCount`: product certifying an entire transcript.

## Main results

* `replayPathCount_mem_SharpP`: polynomial-time replay of `#P` counts has a `#P` path count.
* `replayPathCount_pos_iff`: positivity characterizes the canonical oracle transcript.
* `replayPathCount_le_one`: unambiguous answer counts give unambiguous path counts.
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeMachine
  _root_.Turing.MultiTapePTM Finset

variable {α : Type} {enc : α ↪ List Bool}
variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]

/-- The instruction's certificate count: the appropriate oracle count at a query, and `1` for
canonical `false` padding or `0` for `true` padding at a local or halted instruction. -/
private def replayStepFactor (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (fYes fNo : List Bool → ℕ)
    (x : (α × List Bool) × ℕ) : ℕ :=
  let ((a, answers), index) := x
  let cfg := machine.replayPrefix (input a) answers index
  if (machine.pendingQuery cfg).isSome then
    let q := machine.pendingRequest cfg
    if answers.getD index false then fYes q else fNo q
  else
    if answers.getD index false then 0 else 1

/-- The `#P` product certifying all instructions of transcript `x.2` on instance `x.1`. -/
def replayPathCount (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (fYes fNo : List Bool → ℕ)
    (x : α × List Bool) : ℕ :=
  ∏ i ∈ range x.2.length, replayStepFactor machine input fYes fNo (x, i)

/-- Polynomial-time replay and `#P` oracle certificate counts give a `#P` step factor. -/
private theorem replayStepFactor_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM k Bool Control Operation) {input : α → List Bool}
    {fYes fNo : List Bool → ℕ}
    (hinput : ComputableInPolyTime input enc encBits)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits) :
    replayStepFactor machine input fYes fNo ∈ SharpP (encPair (encPair enc encBits) encUnary) := by
  let _ := Fintype.ofFinite Operation
  let cfg : (α × List Bool) × ℕ → FiniteConfig k Bool Control Operation :=
    fun x => machine.replayPrefix (input x.1.1) x.1.2 x.2
  have hcfg : ComputableInPolyTime cfg
      (encPair (encPair enc encBits) encUnary) encFiniteConfig :=
    machine.computableInPolyTime_replayPrefix.comp (g := fun x : (α × List Bool) × ℕ =>
      ((input x.1.1, x.1.2), x.2)) (by fun_prop)
  have hquery : ComputableInPolyTime
      (fun x => (machine.pendingQuery (cfg x)).isSome)
      (encPair (encPair enc encBits) encUnary) encBool :=
    (ComputableInPolyTime.of_finite Option.isSome).comp
      (machine.pendingQuery_pt.comp hcfg)
  have hreq : ComputableInPolyTime
      (fun x => machine.pendingRequest (cfg x))
      (encPair (encPair enc encBits) encUnary) encBits :=
    machine.pendingRequest_pt.comp hcfg
  have hbit : ComputableInPolyTime
      (fun x : (α × List Bool) × ℕ => x.1.2.getD x.2 false)
      (encPair (encPair enc encBits) encUnary) encBool := by fun_prop
  exact SharpP.ite_mem hquery
    (SharpP.ite_mem hbit (SharpP.comp_mem hYes hreq)
      (SharpP.comp_mem hNo hreq))
    (SharpP.ite_mem hbit SharpP.zero_mem SharpP.one_mem)

/-- The product of the instruction certificate counts is in `#P`. -/
theorem replayPathCount_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM k Bool Control Operation) {input : α → List Bool}
    {fYes fNo : List Bool → ℕ}
    (hinput : ComputableInPolyTime input enc encBits)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits) :
    replayPathCount machine input fYes fNo ∈ SharpP (encPair enc encBits) :=
  SharpP.prod_range_mem (replayStepFactor_mem_SharpP machine hinput hYes hNo)
    (r := fun x : α × List Bool => x.2.length) (by fun_prop)

/-- A step factor is positive exactly when the transcript supplies the canonical reply or
padding. -/
private theorem replayStepFactor_pos_iff (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (a : α) (answers : List Bool) (i : ℕ) :
    0 < replayStepFactor machine input fYes fNo ((a, answers), i) ↔
      answers.getD i false =
        let cfg := machine.replayPrefix (input a) answers i
        if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false := by
  unfold replayStepFactor
  dsimp only
  set cfg := machine.replayPrefix (input a) answers i
  cases hq : (machine.pendingQuery cfg).isSome
  · cases hb : answers.getD i false <;> simp
  · cases hb : answers.getD i false
    · simp [← hNo (machine.pendingRequest cfg)]
    · simp [← hYes (machine.pendingRequest cfg)]

/-- A path count is positive exactly on the canonical instruction-indexed oracle transcript. -/
theorem replayPathCount_pos_iff (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (a : α) (answers : List Bool) :
    0 < replayPathCount machine input fYes fNo (a, answers) ↔
      answers = machine.oracleReplies g answers.length (input a) := by
  unfold replayPathCount
  rw [CanonicallyOrderedAdd.prod_pos, machine.eq_oracleReplies_iff]
  simp only [mem_range,
    replayStepFactor_pos_iff machine input hYes hNo a answers]

/-- Unambiguous oracle certificate counts give an unambiguous step certificate. -/
private theorem replayStepFactor_le_one (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (x : (α × List Bool) × ℕ) :
    replayStepFactor machine input fYes fNo x ≤ 1 := by
  unfold replayStepFactor
  dsimp only
  split_ifs <;> first | exact hYes_le _ | exact hNo_le _ | omega

/-- Unambiguous oracle certificate counts give an unambiguous transcript certificate. -/
theorem replayPathCount_le_one (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (x : α × List Bool) :
    replayPathCount machine input fYes fNo x ≤ 1 :=
  Finset.prod_le_one fun i _ =>
    replayStepFactor_le_one machine input hYes_le hNo_le (x, i)

end Cslib.Complexity
