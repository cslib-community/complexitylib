/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterMethods

/-!
# FIFO correctness of the physical-array memory programs

The count inputs and results are ordinary values; the physical memory assertions reuse
`Block.HoldsList`. The conclusions identify the existing `pairStep` on the front and rear
lists, including empty dequeue and a returned zero. No count cell or stronger room premise is
introduced. The native register representation and paid dispatcher are separate consumers.

## Main results

* `enqueue_contents`: the rear write implements a logical stack push and frames the front.
* `popFront_contents`: the top read implements a logical stack pop without clearing memory.
* `dequeue_contents`: transfer and pop implement the existing FIFO transition `pairStep`.

## References

The queue and its algorithmic references are in `Cslib.DataStructure.Queue.Spec`.
-/

public section

namespace Cslib.DataStructure.Queue.WordRAM.RegisterMetadata

open Cslib.WordRAM Cslib.WordRAM.Realization

/-- Enqueue appends one physical rear word while retaining the entire represented front. -/
theorem enqueue_contents {d : Input} (front back : List ℕ) (s : Memory.State)
    (hF : d 0 = front.length) (hB : d 1 = back.length)
    (hc : front.length + back.length < d 3)
    (hfront : Block.HoldsList (d 2) front.reverse s.mem)
    (hback : Block.HoldsList (d 2 + d 3) back.reverse s.mem) :
    let t := (Memory.spec 0).clientState s (enqueue d)
    (Memory.spec 0).clientResult s (enqueue d) = (front.length, (d 4 :: back).length) ∧
      Block.HoldsList (d 2) front.reverse t.mem ∧
      Block.HoldsList (d 2 + d 3) (d 4 :: back).reverse t.mem := by
  refine ⟨?_, ?_, ?_⟩
  · change (d 0, d 1 + 1) = _
    rw [hF, hB]
    rfl
  · change Block.HoldsList (d 2) front.reverse
      (Function.update s.mem (d 2 + d 3 + d 1) (d 4))
    apply hfront.frame
    intro a ha hb
    rw [Function.update_of_ne]
    simp only [List.length_reverse] at hb
    omega
  · change Block.HoldsList (d 2 + d 3) (d 4 :: back).reverse
      (Function.update s.mem (d 2 + d 3 + d 1) (d 4))
    simpa only [hB, List.reverse_cons, List.length_reverse] using hback.append_one (d 4)

/-- Pop observes the top represented value and retains the unused dirty cell. No memory
clearing, capacity fit or nonzero-value hypothesis is needed for this source equation. -/
theorem popFront_contents {d : Input} (front back : List ℕ) (s : Memory.State)
    (hF : d 0 = front.length) (hB : d 1 = back.length)
    (hfront : Block.HoldsList (d 2) front.reverse s.mem)
    (hback : Block.HoldsList (d 2 + d 3) back.reverse s.mem) :
    (Memory.spec 0).clientResult s (popFront d) =
        ((front.tail.length, back.length), front.head?) ∧
      Block.HoldsList (d 2) front.tail.reverse s.mem ∧
      Block.HoldsList (d 2 + d 3) back.reverse s.mem := by
  cases front with
  | nil =>
    refine ⟨?_, Block.holdsList_nil _ _, hback⟩
    have hz : d 0 = 0 := hF
    rw [clientResult_popFront, ite_eq_left hz, hF, hB]
    rfl
  | cons a front =>
    have hn : d 0 ≠ 0 := by rw [hF]; exact Nat.succ_ne_zero _
    have hlen : d 0 - 1 = front.length := by rw [hF]; rfl
    have hp : Block.HoldsList (d 2) (front.reverse ++ [a]) s.mem := by
      simpa only [List.reverse_cons] using hfront
    have hv : s.mem (d 2 + front.length) = a := by
      have hv : s.mem (d 2 + front.reverse.length) = a :=
        (hp.get front.reverse.length (by simp)).trans (List.getElem_concat_length rfl _)
      simpa only [List.length_reverse] using hv
    refine ⟨?_, ?_, hback⟩
    · rw [clientResult_popFront, ite_eq_right hn, hlen, hB, hv]
      rfl
    · simpa only [List.tail_cons, List.take_left] using
        hp.take front.reverse.length

/-- The interpreter's actual counts, option answer and physical arrays implement the
existing two-stack transition. The only capacity premise is the original sum bound. -/
theorem dequeue_contents {w : ℕ} {d : Input} (front back : List ℕ) (s : Memory.State)
    (hw : Memory.WellFormed w s) (hF : d 0 = front.length) (hB : d 1 = back.length)
    (hc : front.length + back.length ≤ d 3) (hf : d 2 + 2 * d 3 ≤ s.frontier)
    (hfront : Block.HoldsList (d 2) front.reverse s.mem)
    (hback : Block.HoldsList (d 2 + d 3) back.reverse s.mem) :
    let p := pairStep (front, back) .dequeue
    let t := (Memory.spec 0).clientState s (dequeue d)
    (Memory.spec 0).clientResult s (dequeue d) = ((p.1.1.length, p.1.2.length), p.2) ∧
      Block.HoldsList (d 2) p.1.1.reverse t.mem ∧
      Block.HoldsList (d 2 + d 3) p.1.2.reverse t.mem := by
  cases front with
  | nil =>
    have hz : d 0 = 0 := hF
    have hdom : transferDomain w d s := by
      exact ⟨by rw [hF, hB]; exact hc, hf⟩
    have hi := transfer_invariant hw hdom
    have hr : (Memory.spec 0).clientResult s (transfer d) = (back.length, 0) := by
      simpa only [hF, hB, List.length_nil, Nat.zero_add] using hi.2.2.1
    let t := (Memory.spec 0).clientState s (transfer d)
    have ht : Block.HoldsList (d 2) back.reverse.reverse t.mem := by
      simpa only [List.append_nil] using transfer_contents back [] s hF hB hc hfront hback
    have hp := popFront_contents (d := ![back.length, 0, d 2, d 3, d 4])
      back.reverse [] t (by simp) rfl ht (Block.holdsList_nil _ _)
    have hs : (Memory.spec 0).clientState s (dequeue d) = t := by
      rw [dequeue, ite_eq_left hz, StateTransitionSpec.clientState_bind, hr]
      exact clientState_popFront _ _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [dequeue, ite_eq_left hz, StateTransitionSpec.clientResult_bind, hr]
      exact hp.1
    · rw [hs]
      exact hp.2.1
    · rw [hs]
      exact hp.2.2
  | cons a front =>
    have hn : d 0 ≠ 0 := by rw [hF]; exact Nat.succ_ne_zero _
    have hp := popFront_contents (a :: front) back s hF hB hfront hback
    have hs : (Memory.spec 0).clientState s (dequeue d) = s := by
      rw [dequeue, ite_eq_right hn, clientState_popFront]
    refine ⟨?_, ?_, ?_⟩
    · rw [dequeue, ite_eq_right hn]
      exact hp.1
    · rw [hs]
      exact hp.2.1
    · rw [hs]
      exact hp.2.2

end Cslib.DataStructure.Queue.WordRAM.RegisterMetadata
