/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingLoop
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingPrimes
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingFinish
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingWidth

/-!
# Composing every computed native preprocessing root

Starting from the complete frontend's actual output, the native program computes its shared
prime table and reservations, then executes every actual descriptor and recursion tree.

## Main results

* `afterFrontend_exec`: the complete native suffix has exact finite node output and charged cost.

The native composition proofs are original. No runtime algorithm or fit advice is supplied.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- The complete actual suffix consumes only computed frontend output and a global width. -/
theorem afterFrontend_exec {κ w : ℕ} (input : List ℤ) (rs : List (ℕ × ℕ)) (x : Data 128)
    (hw : width κ input.length ≤ w + 2) (hx : x.Bounded (w + 2))
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    (hfront : Frontend.Output (Frontend.layout κ input.length)
      ((input.length + 2) ^ κ) rs x.mem)
    (hparams : Parameters.Output input.length ((input.length + 2) ^ κ)
      (x.comap Frontend.parameterRegisters))
    (hbase : x.regs Frontend.descriptorBase = (Frontend.layout κ input.length).descriptors)
    (hcount : x.regs Frontend.descriptorCount = (Frontend.layout κ input.length).count)
    (hend : x.regs Frontend.heapEnd = (Frontend.layout κ input.length).endpoint)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hnd : (rs.map Prod.fst).Nodup) (hcard : rs.length ≤ input.length) :
    let n := input.length
    let U := (n + 2) ^ κ
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
    let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
    let l := Frontend.layout κ n
    ∃ (out : List (ℕ × Node)) (y : Data 128),
      ExecWithin (w + 2) afterFrontend x y
        ((m + 1) * (7 * m + 15) + 8 + 4 * F + 45 +
          l.count * (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17)) ∧
      out.map Prod.snd = Traversal.Math.output (Nat.primesLE m) l.digits
        ((entries l U rs).map Traversal.Entry.task) ∧
      Traversal.StoredNodes (2 * U) (2 * m ^ 2) (arena κ n x.mem).table out y.mem ∧
      y.regs Traversal.outputCount = out.length ∧
      y.regs Traversal.outputs = (arena κ n x.mem).table ∧
      y.regs packedLength = 8 * m ^ 2 := by
  let n := input.length
  let l := Frontend.layout κ n
  let U := (n + 2) ^ κ
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  have hfits := setup_fits hw x.mem
  obtain ⟨p, hp, ps, pm⟩ := snapshot_exec x hparams hbase hcount hend hfits.2.2.2
  obtain ⟨q, hq, qs, qm, qcount, qbitmap, qprefix⟩ := primes_exec p ps hfits.2.1
  obtain ⟨r, hr, rsaved, rcontrols, rcount, rpower, rremaining, rscalar, rm⟩ :=
    setupTraversal_exec q qs qcount (setup_fits hw q.mem).1
  obtain ⟨b, hb, bs, bcontrols, bcount, bheap, _, _, bm⟩ :=
    finish_exec r rsaved rcontrols rcount rpower rremaining rscalar
      (setup_fits hw r.mem).2.2.1
      ((setup_fits hw r.mem).1.of_le (by omega))
  let a := arena κ n q.mem
  have bmem : b.mem = q.mem := bm.trans rm
  have bcontrol : a.Controls b := by simpa only [rm] using bcontrols
  have bh : b.regs Traversal.heap = a.floor := by simpa only [rm] using bheap
  have bfront : Frontend.Output l U rs b.mem := by
    rw [bmem]
    apply hfront.frame hcard
    intro v hv
    exact (qprefix v hv).trans (congrFun pm v)
  have bbounded := hb.bounded (hr.bounded (hq.bounded (hp.bounded hx)))
  have hi : (ForestCursor.mk 0 []).Invariant a w l U rs b := by
    constructor
    · exact bbounded
    · exact bcontrol
    · exact bfront
    · exact bs.base
    · exact bs.count
    · exact bs.index
    · exact bs.fuel
    · exact bs.stride
    · exact bs.one
    · exact Nat.zero_le _
    · intro v hv
      rw [bmem]
      exact qbitmap v hv
    · exact bh.ge
    · rw [bh]
      exact le_rfl
    · exact bcount
    · simp only [List.length_nil, Nat.sub_zero, Nat.zero_add]
      exact Nat.mul_le_mul_left l.count (work_le_power F)
    · exact Traversal.storedNodes_nil _ _ _ _
    · intro i
      exact Fin.elim0 i
    · simp only [List.map_nil, List.drop_zero, List.nil_append]
    · intro v _
      exact congrFun bmem v
  have hready : a.Ready w := by
    have hh := arena_ready hw q.mem
    simpa only [Nat.add_sub_cancel] using hh
  obtain ⟨s, y, he, hy, _, hout⟩ := forest_exec (arena_separated κ n q.mem) hready hi
    rfl rfl rfl (arena_frontend_before κ n q.mem) hkeys hnd hcard hvalues
  refine ⟨s.nodes, y, ?_, hout, hy.output, hy.count, hy.controls.2.2.2.2.2.2.1, ?_⟩
  · have htotal := hp.within.seq (hq.seq (hr.within.seq (hb.seq he)))
    exact htotal.mono (by
      dsimp only [n, l, U, m, F, a, arena] at *
      simp only [Nat.sub_zero] at *
      omega)
  · have hpersist : forest.Preserves packedLength := body_preserves _ (by decide)
      (by decide) (by decide)
    exact (he.regs_eq hpersist).trans bs.length

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
