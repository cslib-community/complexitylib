/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterMetadata
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Tactic.Realize

/-!
# Queue transfer with explicit register metadata

Both stack counts are explicit input and result words. The source uses the existing memory
programs and bounded while, writes only the original two physical arrays, and neither allocates
count cells nor changes unallocated memory. The remaining rear count is the loop rank.

## Main definitions

* `transfer`: the remaining-count loop over the shared physical transfer step.
* `transferDomain`: the old combined-capacity and physical frontier envelope.

## Main results

* `realizes_transfer`: one native emitter before every count, layout, width and memory.
* `realizes_transfer_standard`: the same semantics on the original standard word-RAM basis.
* `transfer_invariant`: valid histories, exact two-query-per-item cost, count and memory frame.
* `transfer_contents`: the physical arrays have exactly the original reversal semantics.

## References

The queue and its algorithmic references are in `Cslib.DataStructure.Queue.Spec`.
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.WordRAM.RegisterMetadata

open Cslib.WordRAM Cslib.WordRAM.Realization

/-- Reuse the shared physical step with the current two count words. -/
def transferBody (d : Input × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  move ![d.2.1, d.2.2, d.1 2, d.1 3, d.1 4]

/-- Move the whole rear, using the explicit rear count as a sufficient ghost cutoff. -/
def transfer (d : Input) : Memory.Prog (ℕ × ℕ) :=
  boundedWhile (fun _ m => 0 < m.2) transferBody d (d 1) (d 0, d 1)

/-- Both arrays use the old `2*C` physical room; the two counts occupy registers. -/
def transferDomain (_w : ℕ) (d : Input) (s : Memory.State) : Prop :=
  d 0 + d 1 ≤ d 3 ∧ d 2 + 2 * d 3 ≤ s.frontier

/-- The canonical tactic certifies the actual memory-query loop. Every guard and count-copy
instruction is paid through the existing realization factor. -/
theorem realizes_transfer : Realizes .exact transfer (.refl Input) counts
    transferDomain (fun _ _ => 0) := by
  change Realizes .exact transfer (.refl (Fin 5 → ℕ)) counts _ _
  realize
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

/-- The existing defined-evaluation simulation gives the same literal memory semantics on the
standard word-RAM basis used by the original queue. No overflow/underflow behavior is weakened. -/
theorem realizes_transfer_standard : Realizes .standard transfer (.refl Input) counts
    transferDomain (fun _ _ => 0) :=
  realizes_transfer.mapSimulates Basis.Simulates.exactStandard

private theorem transfer_summary (d : Input) (F n : ℕ) {w : ℕ} {s : Memory.State}
    (hw : Memory.WellFormed w s) (hc : F + n ≤ d 3)
    (hf : d 2 + 2 * d 3 ≤ s.frontier) :
    let p := boundedWhile (fun _ m => 0 < m.2) transferBody d n (F, n)
    let t := (Memory.spec 0).clientState s p
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
      Memory.WellFormed w t ∧ (Memory.spec 0).clientResult s p = (F + n, 0) ∧
      t.frontier = s.frontier ∧ memoryCost p s = 2 * n ∧
      Modifies (Block.mk (d 2) (2 * d 3)).footprint s.mem t.mem := by
  induction n generalizing F s with
  | zero => exact ⟨trivial, hw, rfl, rfl, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    let b := transferBody (d, (F, n + 1))
    let t₁ := (Memory.spec 0).clientState s b
    have hdom : domain w ![F, n + 1, d 2, d 3, d 4] s :=
      ⟨Nat.zero_lt_succ n, hc, hf⟩
    have hvb : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s b) :=
      valid_move hw hdom
    have hw₁ : Memory.WellFormed w t₁ := by
      change Memory.WellFormed w ((Memory.spec 0).clientState s b)
      rw [← clientState_width w, ← (Memory.spec w).run_runClient]
      exact hw.run hvb
    have hresult : (Memory.spec 0).clientResult s b = (F + 1, n) := rfl
    have hfrontier : t₁.frontier = s.frontier := rfl
    obtain ⟨hvt, hwt, hrt, hft, hct, hmt⟩ := ih (F + 1) hw₁ (by omega) (by
      rw [hfrontier]
      exact hf)
    let rest := boundedWhile (fun _ m => 0 < m.2) transferBody d n
    have hstate : (Memory.spec 0).clientState s
        (boundedWhile (fun _ m => 0 < m.2) transferBody d (n + 1) (F, n + 1)) =
        (Memory.spec 0).clientState t₁ (rest (F + 1, n)) := by
      change (Memory.spec 0).clientState s (b.bind rest) = _
      simp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind]
      change (Memory.spec 0).clientState t₁ (rest ((Memory.spec 0).clientResult s b)) = _
      rw [hresult]
    refine ⟨?_, hstate ▸ hwt, ?_, hstate ▸ hft.trans hfrontier, ?_, ?_⟩
    · change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (b.bind rest))
      apply (validHistory_bind w b rest s).mpr
      refine ⟨hvb, ?_⟩
      rw [clientState_width w, clientResult_width w, hresult]
      exact hvt
    · change (Memory.spec 0).clientResult s (b.bind rest) = _
      simp only [StateTransitionSpec.clientResult, StateTransitionSpec.runClient_bind]
      change (Memory.spec 0).clientResult t₁ (rest ((Memory.spec 0).clientResult s b)) = _
      rw [hresult, hrt]
      congr 1
      omega
    · change memoryCost (b.bind rest) s = _
      rw [memoryCost_bind, hresult, hct]
      have hb : memoryCost b s = 2 := rfl
      omega
    · intro j hj
      rw [hstate]
      exact (hmt j hj).trans (move_modifies (w := 0) hdom j hj)

/-- Transfer is valid on arbitrary well-formed physical memory under the original room
envelope. It performs exactly two memory queries per moved element and preserves the entire
memory outside the old `2*C` block. The two returned counts are the actual final counts. -/
theorem transfer_invariant {w : ℕ} {d : Input} {s : Memory.State}
    (hw : Memory.WellFormed w s) (h : transferDomain w d s) :
    let t := (Memory.spec 0).clientState s (transfer d)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (transfer d)) ∧
      Memory.WellFormed w t ∧ (Memory.spec 0).clientResult s (transfer d) = (d 0 + d 1, 0) ∧
      t.frontier = s.frontier ∧ memoryCost (transfer d) s = 2 * d 1 ∧
      Modifies (Block.mk (d 2) (2 * d 3)).footprint s.mem t.mem :=
  transfer_summary d (d 0) (d 1) hw h.1 h.2

private theorem transfer_contents_aux (d : Input) (back front : List ℕ) (s : Memory.State)
    (hc : front.length + back.length ≤ d 3)
    (hfront : Block.HoldsList (d 2) front.reverse s.mem)
    (hback : Block.HoldsList (d 2 + d 3) back.reverse s.mem) :
    Block.HoldsList (d 2) (back.reverse ++ front).reverse
      ((Memory.spec 0).clientState s
        (boundedWhile (fun _ m => 0 < m.2) transferBody d back.length
          (front.length, back.length))).mem := by
  induction back generalizing front s with
  | nil =>
    simpa only [List.length_nil, boundedWhile, StateTransitionSpec.clientState,
      StateTransitionSpec.runClient_pure', List.reverse_nil, List.nil_append] using hfront
  | cons v back ih =>
    have hread : s.mem (d 2 + d 3 + back.length) = v := by
      simpa [List.reverse_cons] using hback.get back.length (by simp)
    let t : Memory.State := ⟨Function.update s.mem (d 2 + front.length) v, s.frontier⟩
    have hfront' : Block.HoldsList (d 2) (v :: front).reverse t.mem := by
      simpa only [t, List.reverse_cons, List.length_reverse] using hfront.append_one v
    have hback' : Block.HoldsList (d 2 + d 3) back.reverse t.mem := by
      have hprefix : Block.HoldsList (d 2 + d 3) back.reverse s.mem := by
        simpa [List.reverse_cons] using hback.take back.length
      apply hprefix.frame
      intro a ha _
      exact Function.update_of_ne (by have := hc; simp only [List.length_cons] at this; omega) _ _
    have hc' : (v :: front).length + back.length ≤ d 3 := by
      simp only [List.length_cons] at hc ⊢
      omega
    have hi := ih (v :: front) t hc' hfront' hback'
    let b := transferBody (d, (front.length, (v :: back).length))
    have hrun : (Memory.spec 0).runClient s b =
        ((front.length + 1, back.length), t,
          [Memory.Op.read (d 2 + d 3 + back.length), Memory.Op.write (d 2 + front.length) v]) := by
      change ((front.length + 1, back.length),
        (⟨Function.update s.mem (d 2 + front.length)
          (s.mem (d 2 + d 3 + back.length)), s.frontier⟩ : Memory.State),
        [Memory.Op.read (d 2 + d 3 + back.length), Memory.Op.write (d 2 + front.length)
          (s.mem (d 2 + d 3 + back.length))]) = _
      rw [hread]
    have hstate : (Memory.spec 0).clientState s
        (boundedWhile (fun _ m => 0 < m.2) transferBody d (v :: back).length
          (front.length, (v :: back).length)) =
        (Memory.spec 0).clientState t
          (boundedWhile (fun _ m => 0 < m.2) transferBody d back.length
            ((v :: front).length, back.length)) := by
      change (Memory.spec 0).clientState s
        (b.bind (boundedWhile (fun _ m => 0 < m.2) transferBody d back.length)) = _
      simp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind, hrun,
        List.length_cons]
    rw [hstate]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hi

/-- The physical arrays have exactly the original transfer semantics: the reversed rear is
placed on top of the front. This proof reuses the generic list-array append, prefix and frame
lemmas; no machine step table or count-cell representation is introduced. -/
theorem transfer_contents {d : Input} (back front : List ℕ) (s : Memory.State)
    (hF : d 0 = front.length) (hB : d 1 = back.length)
    (hc : front.length + back.length ≤ d 3)
    (hfront : Block.HoldsList (d 2) front.reverse s.mem)
    (hback : Block.HoldsList (d 2 + d 3) back.reverse s.mem) :
    Block.HoldsList (d 2) (back.reverse ++ front).reverse
      ((Memory.spec 0).clientState s (transfer d)).mem := by
  simpa only [transfer, hF, hB] using transfer_contents_aux d back front s hc hfront hback

end Cslib.DataStructure.Queue.WordRAM.RegisterMetadata
