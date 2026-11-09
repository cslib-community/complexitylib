/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Feedback
public import CslibFrontier.Computability.Probabilistic.NativeBatch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Tactic

/-!
# Executed fresh-block batch planning for native retention

A concrete scheduler partitions the finitely labeled opportunities into consecutive
blocks. Before each response it forms every query in the next block from the actual
runtime context (original instance, previous replies and private word). The block
width and opportunity interface are fixed program parameters; the instance and
unbounded replies are runtime data. This is not compilation of arbitrary schedulers.

The source conventions are [Wang2027], model pp. 4--6 and Theorem 5 p. 12/App. A.5
p. 16. Batch admission is distinct from productivity/cost envelopes. Integral
reservations do not themselves measure physical time. External encodings,
general measurable kernels and unrestricted source Theorems 5/6 remain open.

## Main definitions

* `slots`, `request`: preformed next-block requests containing the actual runtime context.
* `consumed`: all source labels in earlier blocks.

## Main results

* `fresh`, `consumed_succ`, `decode_request`: derived nonreuse, accounting and packet validity.
* `exists_native_controller`: constructed blank-input same-code batch execution law.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchPlanner
open Turing Turing.MultiTapeTM NativeOpenExecution ConcurrentBatch

/-- The concrete planner's next block index, read from the updated runtime counter. -/
@[expose] def stage (n : ℕ) (state : RuntimeControl.State) : ℕ := n - state.opportunities

/-- All queries in a block are preformed from the old state, including hidden
selector bytes and original instance. No response to this batch enters its requests. -/
@[expose] def slots (n width : ℕ) (state : RuntimeControl.State) : Fin n → Option Word :=
  fun i => if i.val / width = stage n state then
    some (frame (RuntimeControl.encoding state)) else none

/-- Actual source-codec bytes, rather than the raw framed State transport. -/
@[expose] def request (n width : ℕ) (state : RuntimeControl.State) : Word :=
  encodeSlots n (slots n width state)

/-- Precisely the labels consumed by earlier consecutive blocks. -/
@[expose] def consumed (n width turn : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val / width < turn

/-- Computed active labels depend only on the block index, not on payload bytes. -/
theorem active_slots (n width : ℕ) (state : RuntimeControl.State) :
    active (slots n width state) = Finset.univ.filter
      (fun i : Fin n => i.val / width = stage n state) := by
  unfold active slots
  apply Finset.filter_congr
  intro i _
  split_ifs <;> simp_all

/-- The next block is disjoint from all earlier blocks, without an admission premise. -/
theorem fresh (n width : ℕ) (state : RuntimeControl.State) :
    Disjoint (active (slots n width state)) (consumed n width (stage n state)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hu
  have he : i.val / width = stage n state := by
    by_contra h
    simp [active, slots, h] at hi
  have hl : i.val / width < stage n state := by simpa [consumed] using hu
  omega

/-- Consuming the next entire batch advances the actual used-label set by one block. -/
theorem consumed_succ (n width : ℕ) (state : RuntimeControl.State) :
    active (slots n width state) ∪ consumed n width (stage n state) =
      consumed n width (stage n state + 1) := by
  ext i
  by_cases h : i.val / width = stage n state <;>
    simp [active, consumed, slots, h]; omega

/-- Before the finite block budget is exhausted, the computed batch is nonempty. -/
theorem nonempty (n width : ℕ) (state : RuntimeControl.State) (hw : 0 < width)
    (hs : stage n state * width < n) : (active (slots n width state)).Nonempty := by
  let i : Fin n := ⟨stage n state * width, hs⟩
  refine ⟨i, ?_⟩
  simp [active, slots, i, hw.ne']

/-- The actual bytes decode as a nonempty batch, whose slots were already fixed. -/
theorem decode_request (n width : ℕ) (state : RuntimeControl.State) (hw : 0 < width)
    (hs : stage n state * width < n) :
    decodeBatch n (request n width state) =
      some ⟨slots n width state, nonempty n width state hw hs⟩ :=
  decodeBatch_encode ⟨slots n width state, nonempty n width state hw hs⟩

private theorem framed_identity : ComputableInPolyTime
    (fun state : RuntimeControl.State => state)
    (RuntimeControl.encoding.trans NativeReplyContext.framedBits) RuntimeControl.encoding := by
  have he : ComputableInPolyTime
      (fun state : RuntimeControl.State => frame (RuntimeControl.encoding state))
      (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encBits :=
    .of_eq fun _ => by rw [Function.Embedding.trans_apply]; rfl
  apply (ComputableInPolyTime.unframe.comp he).of_enc_eq
  intro state
  simp only [encBits_apply, Function.comp_apply, unframe_frame]

private theorem computable_stage (n : ℕ) : ComputableInPolyTime (stage n)
    (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encUnary :=
  ComputableInPolyTime.unary_sub.comp ((ComputableInPolyTime.const n).prod
    (RuntimeControl.computable_opportunities.comp framed_identity))

private theorem computable_slots (total : ℕ) : ∀ (n : ℕ) (group : Fin n → ℕ),
    ComputableInPolyTime (fun state : RuntimeControl.State => encodeSlots n
      (fun i => if group i = stage total state then
        some (frame (RuntimeControl.encoding state)) else none))
      (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encBits := by
  intro n
  induction n with
  | zero => intro group; exact .const []
  | succ n ih =>
    intro group
    have hs := computable_stage total
    have htest := ComputableInPolyTime.decide_and
      (ComputableInPolyTime.unary_le' (ComputableInPolyTime.const (group 0)) hs)
      (ComputableInPolyTime.unary_le' hs (ComputableInPolyTime.const (group 0)))
    have heq : ComputableInPolyTime
        (fun state => decide (group 0 = stage total state))
        (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encBool := by
      simpa only [le_antisymm_iff] using htest
    have hp : ComputableInPolyTime
        (fun state : RuntimeControl.State => frame (RuntimeControl.encoding state))
        (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encBits :=
      .of_eq fun _ => by rw [Function.Embedding.trans_apply]; rfl
    have hframe := ComputableInPolyTime.selfDelimitingCode.comp hp
    have htail := ih (fun i => group i.succ)
    have hyes := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
      (ComputableInPolyTime.bitsAppend hframe htail)
    have hno := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false) htail
    have h := ComputableInPolyTime.ite_decide heq hyes hno
    convert h using 1
    funext state
    dsimp only [encodeSlots, Function.comp_apply]
    split_ifs <;> rfl

/-- A constructed pure algorithm forms the whole concurrent packet on actual
runtime State bytes. No executable-scheduler or representation witness is supplied. -/
theorem computable_request (n width : ℕ) : ComputableInPolyTime (request n width)
    (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encBits :=
  computable_slots n n (fun i => i.val / width)

/-- One actual finite native program loads the original input and repeatedly forms
source-batch packets on its query tape, keeping the separate full runtime context
for retention and restart. The joint law includes all raw events and resources;
source acceptance is proved separately from this constructed execution law. -/
theorem exists_native_controller (n batchWidth : ℕ) :
    ∃ (width : ℕ) (R : Type) (_ : Finite R)
      (program : MultiTapePTM width Bool R Unit) (context : Fin width),
      ∀ (P : Type) (env : Environment Unit P) (data : GuardedStartup.Input)
        (memory : Memory Unit P),
        (NativeUnboundedExecution.terminal program env
          ⟨program.initialConfig (GuardedStartup.encoding data), memory⟩).map
          (Option.map (NativeReplyContext.observe context)) =
        let state := GuardedStartup.state data
        (Feedback.run env state.turns state (fun _ => ⟨[], [], 0⟩) memory
          (request n batchWidth)).map fun outcome =>
          some (⟨tapeOfList (RuntimeControl.packet outcome.state),
            RuntimeControl.result outcome.state,
            outcome.memory⟩ : NativeReplyContext.Observation P) :=
  Feedback.exists_native_controller_with_request (request n batchWidth)
    (computable_request n batchWidth)

end Cslib.Probability.StochasticOracle.NativeRetention.BatchPlanner
