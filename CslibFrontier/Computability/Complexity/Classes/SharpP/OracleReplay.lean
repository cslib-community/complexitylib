/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import CslibFrontier.Computability.Complexity.Classes.SharpP.Aggregation
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Complexity.Classes.SharpP.Products
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.OfFn

/-!
# Unsigned certificate counts for oracle replay

Each instruction-indexed transcript receives the product of its oracle certificate counts.
A query contributes the count supporting its guessed answer; a local or halted instruction
contributes `1` for the canonical padding bit `false` and `0` for `true`. Positive path counts
therefore characterize the canonical oracle transcript, and counts bounded by one preserve
unambiguity. These are the common certificates used by the decision and counting lowness proofs.
Weighting each transcript's path count by a `#P` function of its replayed output and summing over
all transcripts of the clock length gives the `#P` function used by those proofs.

## Main definitions

* `replayPathCount`: product certifying an entire transcript.
* `replayWeightedSum`: path counts weighted by a function of the replayed output, summed over all
  transcripts of the clock length.

## Main results

* `replayPathCount_mem_SharpP`: polynomial-time replay of `#P` counts has a `#P` path count.
* `replayPathCount_pos_iff`: positivity characterizes the canonical oracle transcript.
* `replayPathCount_le_one`: unambiguous answer counts give unambiguous path counts.
* `replayWeightedSum_mem_SharpP`: the weighted sum of a `#P` weight is in `#P`.
* `replayWeightedSum_pos_iff`, `replayWeightedSum_eq_of_le_one`: the weighted sum is positive
  exactly when the weight of the canonical replay is, and equals that weight for unambiguous
  answer counts.
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
  -- reindex to the argument shape of the replay-prefix polynomial-time lemmas; the
  -- compositions are elaborated without an expected type, which keeps unification first-order
  have hreplay : ComputableInPolyTime
      (fun x : (α × List Bool) × ℕ => ((input x.1.1, x.1.2), x.2))
      (encPair (encPair enc encBits) encUnary) (encPair (encPair encBits encBits) encUnary) := by
    fun_prop
  have hquery := machine.replayPrefix_isQuery_pt.comp hreplay
  have hreq := machine.replayPrefix_pendingRequest_pt.comp hreplay
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

/-! ### Weighted sums over all transcripts -/

/-- The sum, over all transcripts of length `T a`, of the transcript's path count times the weight
`F` of the instance and the replayed output. -/
def replayWeightedSum (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) (fYes fNo : List Bool → ℕ)
    (F : α × List Bool → ℕ) (a : α) : ℕ :=
  ∑ w : Fin (T a) → Bool,
    replayPathCount machine input fYes fNo (a, List.ofFn w) *
      F (a, machine.replayOutput (input a) (List.ofFn w))

/-- Polynomial-time replay, `#P` oracle certificate counts and a `#P` weight give a `#P`
weighted sum. -/
theorem replayWeightedSum_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM k Bool Control Operation) {input : α → List Bool}
    {T : α → ℕ} {fYes fNo : List Bool → ℕ} {F : α × List Bool → ℕ}
    (hinput : ComputableInPolyTime input enc encBits)
    (hT : ComputableInPolyTime T enc encUnary)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits)
    (hF : F ∈ SharpP (encPair enc encBits)) :
    replayWeightedSum machine input T fYes fNo F ∈ SharpP enc := by
  have hpath := replayPathCount_mem_SharpP machine hinput hYes hNo
  have hpair : ComputableInPolyTime
      (fun x : α × List Bool => (input x.1, x.2))
      (encPair enc encBits) (encPair encBits encBits) := by fun_prop
  have hout : (fun x : α × List Bool => F (x.1, machine.replayOutput (input x.1) x.2)) ∈
      SharpP (encPair enc encBits) :=
    SharpP.comp_mem hF ((ComputableInPolyTime.fst enc encBits).prod
      (machine.computableInPolyTime_replayOutput.comp hpair))
  exact SharpP.sum_bits_mem (SharpP.mul_mem hpath hout) hT

/-- The canonical transcript of the clock length is the transcript of some `w : Fin n → Bool`. -/
private theorem exists_ofFn_eq_oracleReplies (machine : MultiTapePTM k Bool Control Operation)
    (g : List Bool → Bool) (n : ℕ) (input : List Bool) :
    ∃ w : Fin n → Bool, List.ofFn w = machine.oracleReplies g n input := by
  have hlen := machine.length_oracleReplies g n input
  exact ⟨fun i => (machine.oracleReplies g n input)[i.val]'(by omega),
    (List.ofFn_congr hlen.symm _).trans List.ofFn_getElem⟩

/-- The weighted sum is positive exactly when the weight of the canonical replay is: positive
path counts characterize the canonical transcript. -/
theorem replayWeightedSum_pos_iff (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (F : α × List Bool → ℕ) (a : α) :
    0 < replayWeightedSum machine input T fYes fNo F a ↔
      0 < F (a, machine.replayOutput (input a) (machine.oracleReplies g (T a) (input a))) := by
  unfold replayWeightedSum
  simp only [Finset.sum_pos_iff, mem_univ, true_and, CanonicallyOrderedAdd.mul_pos,
    replayPathCount_pos_iff machine input hYes hNo, List.length_ofFn]
  constructor
  · rintro ⟨w, hw, hF⟩
    rwa [← hw]
  · intro hF
    obtain ⟨w, hw⟩ := exists_ofFn_eq_oracleReplies machine g (T a) (input a)
    exact ⟨w, hw, hw ▸ hF⟩

/-- For unambiguous oracle certificate counts the weighted sum is the weight of the canonical
replay: the canonical transcript has path count `1` and every other transcript `0`. -/
theorem replayWeightedSum_eq_of_le_one (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (F : α × List Bool → ℕ) (a : α) :
    replayWeightedSum machine input T fYes fNo F a =
      F (a, machine.replayOutput (input a) (machine.oracleReplies g (T a) (input a))) := by
  obtain ⟨w₀, hw₀⟩ := exists_ofFn_eq_oracleReplies machine g (T a) (input a)
  unfold replayWeightedSum
  rw [Finset.sum_eq_single w₀]
  · have hpos : 0 < replayPathCount machine input fYes fNo (a, List.ofFn w₀) := by
      rw [replayPathCount_pos_iff machine input hYes hNo, List.length_ofFn]
      exact hw₀
    have hle := replayPathCount_le_one machine input hYes_le hNo_le (a, List.ofFn w₀)
    have heq : replayPathCount machine input fYes fNo (a, List.ofFn w₀) = 1 := by omega
    rw [heq, one_mul, hw₀]
  · intro w _ hw
    have hnot : ¬0 < replayPathCount machine input fYes fNo (a, List.ofFn w) := by
      rw [replayPathCount_pos_iff machine input hYes hNo, List.length_ofFn, ← hw₀]
      exact fun h => hw (List.ofFn_injective h)
    have hz : replayPathCount machine input fYes fNo (a, List.ofFn w) = 0 := by omega
    rw [hz, zero_mul]
  · intro hmem
    exact False.elim (hmem (mem_univ w₀))

end Cslib.Complexity
