/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Queue.WordRAM.RegisterTransfer
import Complexity.Tactic.Realize

/-!
# Queue methods with resident register metadata

Both methods consume the same five live words: the two stack counts, base, capacity and the
delivered payload. Their returned vectors begin with the two updated counts. Enqueue has no
logical answer word; dequeue appends the faithful option encoding, including a distinct tag for
`some 0`. The memory programs write only the original two physical arrays.

## Main definitions

* `enqueue`, `popFront`, `dequeue`: memory programs with explicit count inputs and results.
* `enqueueDomain`: spare capacity, physical room and a word-sized delivered value.

## Main results

* `realizes_enqueue`, `realizes_popFront`, `realizes_dequeue`: uniform native method bodies.

## References

The queue and its algorithmic references are in `Cslib.DataStructure.Queue.Spec`.
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.WordRAM.RegisterMetadata

open Cslib.WordRAM Cslib.WordRAM.Realization

/-- Write the rear's next physical cell and return the two new count words. There is no echo
of the delivered payload in the result. -/
def enqueue (d : Input) : Memory.Prog (ℕ × ℕ) := do
  Memory.write (d 2 + d 3 + d 1) (d 4)
  pure (d 0, d 1 + 1)

/-- The original queue enqueue domain, with the physical room unchanged. -/
def enqueueDomain (w : ℕ) (d : Input) (s : Memory.State) : Prop :=
  d 0 + d 1 < d 3 ∧ d 2 + 2 * d 3 ≤ s.frontier ∧ Fits w (d 4)

/-- An empty front returns none without a memory query. A nonempty front reads its top and
returns a decremented count; the unused physical cell is retained. -/
def popFront (d : Input) : Memory.Prog ((ℕ × ℕ) × Option ℕ) :=
  if d 0 = 0 then pure ((d 0, d 1), none) else do
    let v ← Memory.read (d 2 + (d 0 - 1))
    pure ((d 0 - 1, d 1), some v)

/-- The front-empty path transfers the rear before performing the original front pop. -/
def dequeue (d : Input) : Memory.Prog ((ℕ × ℕ) × Option ℕ) :=
  if d 0 = 0 then do
    let m ← transfer d
    popFront ![m.1, m.2, d 2, d 3, d 4]
  else popFront d

/-- One uniform enqueue body, with all address arithmetic, result copies and control charged. -/
theorem realizes_enqueue : Realizes .exact enqueue (.refl Input) counts
    enqueueDomain (fun _ _ => 0) := by
  change Realizes .exact enqueue (.refl (Fin 5 → ℕ)) counts _ _
  realize
  · exact hmem.fits_of_lt_frontier (by have := h.1; have := h.2.1; omega)
  · exact (show Fits w (d 3) from hwords 3).of_le (by have := h.1; omega)

/-- A uniform typed pop body; the option tag is separate from its full-range word payload. -/
theorem realizes_popFront : Realizes .exact popFront (.refl Input)
    (appendWords counts optionWords) transferDomain (fun _ _ => 0) := by
  change Realizes .exact popFront (.refl (Fin 5 → ℕ)) _ _ _
  realize
  · omega
  · exact hmem.fits_of_lt_frontier (by have := h.1; have := h.2; omega)
  · exact (show Fits w (d 0) from hwords 0).of_le (by omega)

/-- Dequeue reuses the shared remaining-count transfer and preserves the exact old room. -/
theorem realizes_dequeue : Realizes .exact dequeue (.refl Input)
    (appendWords counts optionWords) transferDomain (fun _ _ => 0) := by
  change Realizes .exact dequeue (.refl (Fin 5 → ℕ)) _ _ _
  realize
  all_goals try omega
  case hsafe.isTrue.left =>
    intro hv
    refine whileSafe_of_measure _ _ _ w d
      (fun m t => Memory.WellFormed w t ∧ m.1 + m.2 ≤ d 3 ∧ d 2 + 2 * d 3 ≤ t.frontier)
      (fun m _ => m.2) (fun m _ _ hz hg => by omega) ?_ ⟨hmem, h.1, h.2⟩ le_rfl hv
    rintro m t ⟨hwt, hcap, hfrontier⟩ hg hb
    refine ⟨?_, ?_, ?_⟩
    · change (1 ≤ m.2 ∧ Fits w (d 2 + d 3 + (m.2 - 1))) ∧
        Fits w (d 2 + m.1) ∧ 1 ≤ m.2 ∧ Fits w (m.1 + 1)
      exact ⟨⟨by omega, hwt.fits_of_lt_frontier (by omega)⟩,
        hwt.fits_of_lt_frontier (by omega), by omega,
        (show Fits w (d 3) from hwords 3).of_le (by omega)⟩
    · have hw' : Memory.WellFormed w
          ((Memory.spec 0).clientState t (move ![m.1, m.2, d 2, d 3, d 4])) := by
        rw [← clientState_width w, ← (Memory.spec w).run_runClient]
        exact hwt.run hb
      refine ⟨hw', ?_, ?_⟩
      · change (m.1 + 1) + (m.2 - 1) ≤ d 3
        omega
      · exact hfrontier
    · change m.2 - 1 < m.2
      omega
  case hsafe.isTrue.right.isFalse.left.right =>
    have hr := (transfer_invariant hmem h).2.2.1
    rw [hr] at hc ⊢
    change d 0 + d 1 ≠ 0 at hc
    change Fits w (d 2 + (d 0 + d 1 - 1))
    exact hmem.fits_of_lt_frontier (by have := h.1; have := h.2; omega)
  case hsafe.isTrue.right.isFalse.right.right =>
    have hr := (transfer_invariant hmem h).2.2.1
    rw [hr] at hc
    change d 0 + d 1 ≠ 0 at hc
    exact (show Fits w (d 3) from hwords 3).of_le (by have := h.1; omega)
  case hsafe.isFalse.isFalse.left.right =>
    exact hmem.fits_of_lt_frontier (by have := h.1; have := h.2; omega)
  case hsafe.isFalse.isFalse.right.right =>
    exact (show Fits w (d 0) from hwords 0).of_le (by omega)

/-- The original standard word-RAM basis has the same checked method behavior. -/
theorem realizes_enqueue_standard : Realizes .standard enqueue (.refl Input) counts
    enqueueDomain (fun _ _ => 0) :=
  realizes_enqueue.mapSimulates Basis.Simulates.exactStandard

/-- Standard-basis dequeue keeps both counts and the faithful option result. -/
theorem realizes_dequeue_standard : Realizes .standard dequeue (.refl Input)
    (appendWords counts optionWords) transferDomain (fun _ _ => 0) :=
  realizes_dequeue.mapSimulates Basis.Simulates.exactStandard

/-- Enqueue issues exactly the physical rear write, retaining the frontier. -/
theorem runClient_enqueue (w : ℕ) (d : Input) (s : Memory.State) :
    (Memory.spec w).runClient s (enqueue d) =
      ((d 0, d 1 + 1), ⟨Function.update s.mem (d 2 + d 3 + d 1) (d 4), s.frontier⟩,
        [.write (d 2 + d 3 + d 1) (d 4)]) := rfl

/-- The spare-capacity domain admits the one physical write, including the delivered value. -/
theorem valid_enqueue {w : ℕ} {d : Input} {s : Memory.State}
    (h : enqueueDomain w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (enqueue d)) := by
  change (d 2 + d 3 + d 1 < s.frontier ∧ Fits w (d 4)) ∧ True
  exact ⟨⟨by have := h.1; have := h.2.1; omega, h.2.2⟩, trivial⟩

/-- Enqueue uses one memory query, independently of the capacity and existing contents. -/
theorem memoryCost_enqueue (d : Input) (s : Memory.State) :
    memoryCost (enqueue d) s = 1 := rfl

/-- The rear write remains inside the original two-array footprint. -/
theorem enqueue_modifies {w : ℕ} {d : Input} {s : Memory.State}
    (h : enqueueDomain w d s) :
    Modifies (Block.mk (d 2) (2 * d 3)).footprint s.mem
      ((Memory.spec w).clientState s (enqueue d)).mem := by
  exact Modifies.write_of_owns ⟨by omega, by have := h.1; omega⟩ _

/-- Pop never changes any memory cell or the frontier, including its empty path. -/
theorem clientState_popFront (w : ℕ) (d : Input) (s : Memory.State) :
    (Memory.spec w).clientState s (popFront d) = s := by
  by_cases hz : d 0 = 0
  · rw [popFront, ite_eq_left hz]
    rfl
  · rw [popFront, ite_eq_right hz]
    rfl

/-- Both returned counts are exact even when the unused physical top cell remains dirty. -/
theorem clientResult_popFront (w : ℕ) (d : Input) (s : Memory.State) :
    (Memory.spec w).clientResult s (popFront d) =
      if d 0 = 0 then ((d 0, d 1), none)
      else ((d 0 - 1, d 1), some (s.mem (d 2 + (d 0 - 1)))) := by
  by_cases hz : d 0 = 0
  · rw [popFront, ite_eq_left hz, ite_eq_left hz]
    rfl
  · rw [popFront, ite_eq_right hz, ite_eq_right hz]
    rfl

/-- A nonempty front performs one read; an empty front performs no memory operation. -/
theorem memoryCost_popFront (d : Input) (s : Memory.State) :
    memoryCost (popFront d) s = if d 0 = 0 then 0 else 1 := by
  by_cases hz : d 0 = 0
  · rw [popFront, ite_eq_left hz, ite_eq_left hz]
    rfl
  · rw [popFront, ite_eq_right hz, ite_eq_right hz]
    rfl

/-- Every nonempty front read lies in the old physical region. -/
theorem valid_popFront {w : ℕ} {d : Input} {s : Memory.State}
    (h : transferDomain w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (popFront d)) := by
  by_cases hz : d 0 = 0
  · rw [popFront, ite_eq_left hz]
    trivial
  · rw [popFront, ite_eq_right hz]
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (do
        let v ← Memory.read (d 2 + (d 0 - 1))
        pure ((d 0 - 1, d 1), some v)))
    change (d 2 + (d 0 - 1) < s.frontier) ∧ True
    exact ⟨by have := h.1; have := h.2; omega, trivial⟩

/-- Dequeue's source summary retains the actual final counts, valid physical history and
frontier. The fallback performs exactly two queries per transferred element and one final
read when the queue was nonempty. -/
theorem dequeue_invariant {w : ℕ} {d : Input} {s : Memory.State}
    (hw : Memory.WellFormed w s) (h : transferDomain w d s) :
    let t := (Memory.spec 0).clientState s (dequeue d)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dequeue d)) ∧
      Memory.WellFormed w t ∧
      ((Memory.spec 0).clientResult s (dequeue d)).1 =
        (if d 0 = 0 then (d 1 - 1, 0) else (d 0 - 1, d 1)) ∧
      t.frontier = s.frontier ∧
      memoryCost (dequeue d) s =
        (if d 0 = 0 then 2 * d 1 + (if d 1 = 0 then 0 else 1) else 1) ∧
      Modifies (Block.mk (d 2) (2 * d 3)).footprint s.mem t.mem := by
  by_cases hz : d 0 = 0
  · obtain ⟨hv, hwt, hr, hf, hc, hm⟩ := transfer_invariant hw h
    have hr' : (Memory.spec 0).clientResult s (transfer d) = (d 1, 0) := by
      simpa only [hz, Nat.zero_add] using hr
    let t := (Memory.spec 0).clientState s (transfer d)
    let e : Input := ![d 1, 0, d 2, d 3, d 4]
    have he : transferDomain w e t := by
      refine ⟨?_, ?_⟩
      · change d 1 + 0 ≤ d 3
        have := h.1
        omega
      · change d 2 + 2 * d 3 ≤ t.frontier
        rw [hf]
        exact h.2
    have hs : (Memory.spec 0).clientState s (dequeue d) = t := by
      rw [dequeue, ite_eq_left hz, StateTransitionSpec.clientState_bind, hr']
      exact clientState_popFront 0 e t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [dequeue, ite_eq_left hz]
      change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        ((transfer d).bind (fun m => popFront ![m.1, m.2, d 2, d 3, d 4])))
      rw [validHistory_bind]
      refine ⟨hv, ?_⟩
      rw [clientState_width w, clientResult_width w, hr']
      exact valid_popFront he
    · rw [hs]
      exact hwt
    · rw [dequeue, ite_eq_left hz, StateTransitionSpec.clientResult_bind, hr',
        clientResult_popFront, ite_eq_left hz]
      change (if d 1 = 0 then ((d 1, 0), none)
        else ((d 1 - 1, 0), some (t.mem (d 2 + (d 1 - 1))))).1 = (d 1 - 1, 0)
      split <;> simp_all
    · rw [hs]
      exact hf
    · rw [dequeue, ite_eq_left hz]
      change memoryCost ((transfer d).bind (fun m => popFront ![m.1, m.2, d 2, d 3, d 4])) s = _
      rw [memoryCost_bind, hr', hc, memoryCost_popFront, ite_eq_left hz]
      rfl
    · rw [hs]
      exact hm
  · have hs : (Memory.spec 0).clientState s (dequeue d) = s := by
      rw [dequeue, ite_eq_right hz, clientState_popFront]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [dequeue, ite_eq_right hz]
      exact valid_popFront h
    · rw [hs]
      exact hw
    · rw [dequeue, ite_eq_right hz, clientResult_popFront, ite_eq_right hz, ite_eq_right hz]
    · rw [hs]
    · rw [dequeue, ite_eq_right hz, memoryCost_popFront, ite_eq_right hz, ite_eq_right hz]
    · rw [hs]
      exact fun _ _ => rfl

/-- At the source-memory boundary, one enqueue pays for its write and the added rear credit.
Native glue and the final halt are accounted for separately by the realized dispatcher. -/
theorem enqueue_memory_amortized (d : Input) (s : Memory.State) :
    memoryCost (enqueue d) s + 2 * ((Memory.spec 0).clientResult s (enqueue d)).2 =
      3 + 2 * d 1 := by
  change 1 + 2 * (d 1 + 1) = _
  omega

/-- The actual transfer queries are paid by the initial rear credit, including a final
nonempty pop. This is a source-memory bound, not a claim that native glue is free. -/
theorem dequeue_memory_amortized {w : ℕ} {d : Input} {s : Memory.State}
    (hw : Memory.WellFormed w s) (h : transferDomain w d s) :
    memoryCost (dequeue d) s + 2 * ((Memory.spec 0).clientResult s (dequeue d)).1.2 ≤
      3 + 2 * d 1 := by
  have hi := dequeue_invariant hw h
  rw [hi.2.2.1, hi.2.2.2.2.1]
  split <;> (try split) <;> simp_all

end Cslib.DataStructure.Queue.WordRAM.RegisterMetadata
