/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Boundary
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorInitialize
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorForest
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorCost
import Complexity.Computability.WordRAM.Call
import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Registers

/-!
# Composing initialized ordinary 3SUM with the native visitor

The actual frontend supplies compact native arrays, multiplicity counts and descriptors. Shared
preparation computes the prime bitmap, conservative arena and value envelope before the forest.
Each node's actual packed block enters the certified Convolution host before its dead packed tail
is released and children are pushed. The forest consumes exactly the finite node preorder,
including repeated occurrences, and folds all answers without early exit.

Each call receives the current allocation endpoint as workspace. Its lower-prefix return frame
retains pending heavy arrays and source data despite arbitrary higher scratch writes. Persistent
heavy-buffer capacities and count cells remain allocated while one charged copy releases each
consumed packed/residue/histogram tail for reuse. The old table gap remains reserved; there is no
ordinary packed-pointer publication or later table readback. The finite Chan–He correctness
theorem gives the same distinct-position 3SUM verdict, and the charged ledger is covered by the
unchanged `Decision.cost` envelope.

`Visitor.live_transition` gives the actual live body's final committed heap as its initial heap
plus three count cells and the sum of current input-column lengths. Skipped bodies leave the heap
unchanged. The emission witness describes the state before release; release lemmas describe the
smaller frontier and retained children. No improved total-space or arbitrary-callee high-water
bound is asserted.

`exec_large` assumes the complete initial register file is physically bounded. The initialized
ordinary endpoint derives this premise from `Data.init` and its actual saved-header prefix; it
adds no hypothesis to that endpoint's magnitude and width contract.

## Main results

* `exec_large`: actual large-input visitor execution, raw Boolean and exact 3SUM verdict.

This native composition is original and reuses the existing finite reduction.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM
open Visitor
open Cslib.Algorithms.ThreeSum (HasSolution Convolution)

/-- Execute the actual visitor after the saved-header prefix at every admitted physical width. -/
theorem exec_large {κ w r : ℕ} (input : List ℤ) (c : Host.Callee r)
    (x : Data (registerCount r))
    (hw : width κ c.widthCoefficient input.length ≤ w) (hx : x.Bounded w)
    (hn : 3 ≤ input.length)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    (hinit : x.comap (preprocessingRegisters r) = Data.init (input.map Signed.encode))
    (hlen : x.regs (controllerRegisters r inputLength) = input.length)
    (hans : x.regs (controllerRegisters r answer) = 0) :
    ∃ y, ExecWithin w (large κ c.code) x y (Decision.cost κ c input.length - 7) ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        HasSolution (fun i : Fin input.length => input[i])) := by
  let n := input.length
  let U := (n + 2) ^ κ
  let l := Frontend.layout κ n
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  let S := 13 + (2 + ((m + 1) * (7 * m + 15) + 8)) + 19 +
    (4 * (F + 1) + 5) + (4 * envelopeExponent κ + 8)
  have hppw := (preprocessing_width_le κ c.widthCoefficient n).trans hw
  have hfrontw := (ChanHe.Preprocessing.frontend_width_le κ n).trans hppw
  have hw2 : w - 2 + 2 = w := by
    have := (four_le_width κ c.widthCoefficient n).trans hw
    omega
  obtain ⟨p, rs, hp, ho, hbase, hcount, hend, hnd, _, hkeys, hcounts, _, _, hparams, _⟩ :=
    Frontend.exec_input input hfrontw hvalues
  have hcard : rs.length ≤ n := by
    have ht := hnd.length_le_of_subset (fun k hk => (hkeys k).mp hk)
    simpa only [List.length_map] using ht
  obtain ⟨q, hq, hqp, hframe⟩ := ExecWithin.rename_post (x := x) (Q := fun q => q = p)
    (preprocessing_injective r) ⟨p, by simpa only [hinit] using hp, rfl⟩
  have hqr (i : Fin 128) : q.regs (preprocessingRegisters r i) = p.regs i :=
    congrArg (fun q => q.regs i) hqp
  have hqm : q.mem = p.mem := congrArg Data.mem hqp
  have hqc (i : Fin 16) : q.regs (controllerRegisters r i) = x.regs (controllerRegisters r i) :=
    hframe _ (fun j => (controller_ne_preprocessing i j).symm)
  obtain ⟨b, hb, hi⟩ := initialize_forest (w := w - 2) rs q
    (by simpa only [hw2] using hw) (by simpa only [hw2] using hq.bounded hx)
    ((hqc _).trans hlen) ((hqc _).trans hans)
    (by simpa only [hqm] using ho) (by simpa only [hqp] using hparams)
    ((hqr _).trans hbase) ((hqr _).trans hcount) ((hqr _).trans hend) hcard
  rw [hw2] at hb
  let a := ChanHe.Preprocessing.arena κ n b.mem
  have hresources := arena_resources κ n b.mem
  obtain ⟨s, y, he, hy, _, hout⟩ := forest_exec (w := w - 2) c
    (by simpa only [hw2] using hw) (ChanHe.Preprocessing.arena_separated κ n b.mem)
    ⟨hresources.1.le, hresources.2⟩ (ChanHe.Preprocessing.arena_ready hppw b.mem)
    hi rfl rfl rfl (ChanHe.Preprocessing.arena_frontend_before κ n b.mem)
    hkeys hnd hcard hvalues
  rw [hw2] at he
  have hnodes := ChanHe.Preprocessing.entries_output hkeys (fun p hp => (hcounts p hp).2) hvalues
  have hnodesA : ChanHe.Traversal.Math.output (Nat.primesLE a.m) a.Λ
      ((ChanHe.Preprocessing.entries l U rs).map ChanHe.Traversal.Entry.task) =
      Cslib.Algorithms.ThreeSum.ChanHe.allNodes n U (fun i : Fin n => input[i]) := hnodes
  have hout' : s.nodes = Cslib.Algorithms.ThreeSum.ChanHe.allNodes n U
      (fun i : Fin n => input[i]) := hout.trans hnodes
  have hN : 4 * a.N = instanceLength κ n := by
    dsimp only [a, ChanHe.Preprocessing.arena, instanceLength, U]
    omega
  refine ⟨y, ?_, hy.boolean, ?_⟩
  · change ExecWithin w (forest c.code) b y
      ((ForestCursor.mk 0 []).credit a l U rs
        (Host.callerTime (4 * a.N)
          (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8) + 2)
      at he
    rw [hN] at he
    change ExecWithin w (forest c.code) b y
      ((ForestCursor.mk 0 []).credit a l U rs (callbackTime κ c n) + 2) at he
    have hcredit : (ForestCursor.mk 0 []).credit a l U rs (callbackTime κ c n) =
        l.count * (ChanHe.Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) +
          (Cslib.Algorithms.ThreeSum.ChanHe.allNodes n U
            (fun i : Fin n => input[i])).length * callbackTime κ c n := by
      change l.count * (ChanHe.Traversal.rootTime a.fuel a.n a.m a.N + 17) +
        (ChanHe.Traversal.Math.output (Nat.primesLE a.m) a.Λ
          ((ChanHe.Preprocessing.entries l U rs).map ChanHe.Traversal.Entry.task)).length *
            callbackTime κ c n = _
      rw [hnodesA]
      rfl
    rw [hcredit] at he
    have hbudget : (Frontend.cost κ n - 1) + S +
        (l.count * (ChanHe.Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) +
          (Cslib.Algorithms.ThreeSum.ChanHe.allNodes n U
            (fun i : Fin n => input[i])).length * callbackTime κ c n + 2) =
        largeCost κ c n (Cslib.Algorithms.ThreeSum.ChanHe.allNodes n U
          (fun i : Fin n => input[i])).length := by
      dsimp only [largeCost, forestCost, S, l, m, F, U]
      omega
    have hcost := allNodes_cost_le κ c n (fun i : Fin n => input[i])
    obtain ⟨tf, htf, hfe⟩ := hq
    obtain ⟨ts, hts, hse⟩ := hb
    obtain ⟨tl, htl, hle⟩ := he
    have hts' : ts ≤ S := hts
    cases hse with
    | seq hprepare hrest =>
      cases hrest with
      | seq henvelope hpower =>
        exact (hfe.seq (hprepare.seq (henvelope.seq (hpower.seq hle)))).within.mono (by
          dsimp only [n, U, m, F, S, l] at htf hts hts' htl hbudget hcost ⊢
          omega)
  · have hv : y.regs (controllerRegisters r answer) = 1 ↔
        ∃ node ∈ s.nodes, Convolution (instanceLength κ n) (node.oneArray (2 * U)) := by
      have hv := hy.verdict
      change y.regs (controllerRegisters r answer) = 1 ↔
        ∃ node ∈ s.nodes, Convolution (4 * a.N) (node.oneArray a.U) at hv
      rw [hN] at hv
      exact hv
    rw [hv, hout']
    have hcorrect := Cslib.Algorithms.ThreeSum.ChanHe.instances_correct n U (by omega)
      (fun i : Fin n => input[i]) (fun i => hvalues _ (List.getElem_mem i.isLt))
    constructor
    · rintro ⟨node, hnode, hconv⟩
      apply hcorrect.mpr
      refine ⟨node.oneArray (2 * U), List.mem_map.mpr ⟨node, hnode, rfl⟩, ?_⟩
      simpa only [instanceLength, U] using hconv
    · intro hsol
      obtain ⟨μ, hμ, hs⟩ := hcorrect.mp hsol
      obtain ⟨node, hnode, rfl⟩ := List.mem_map.mp hμ
      exact ⟨node, hnode, by simpa only [instanceLength, U] using hs⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
