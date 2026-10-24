/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Query.Node

/-!
# Checked pointer-chasing fusion-tree descent

Each iteration reads a tag, compares a leaf or runs an actual node query, and either stops
or loads a child pointer. The proof descends through the represented tree; every followed
child has smaller height. No execution or correctness assumption is hidden in the invariant.

## Main definitions

* `QueryProgram.Done`: postcondition for a stopped fusion-tree traversal.

## Main results

* `QueryProgram.exec_loop`: inclusive predecessor in at most
  `201022 * (height + 1) + 2` instructions, with all RAM memory and query preserved.

## References

* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound with fusion
  trees*][FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.QueryProgram

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree

/-- A stopped traversal returns a conventional option and preserves the original RAM/query. -/
structure Done (q : ℕ) (ans : Option ℕ) (mem : ℕ → ℕ) (y : Data registers) : Prop where
  active_eq : y.regs active = 0
  zero_eq : y.regs zero = 0
  mem_eq : y.mem = mem
  query_eq : y.regs query = q
  found_le : y.regs found ≤ 1
  answer_eq : answer y = ans

/-- The loop condition holds at entry. -/
private theorem Entry.running {q p : ℕ} {x : Data registers} (hx : Entry q p x) :
    (Cond.lt zero active).Holds x := by
  simp only [Cond.holds_lt, hx.zero_eq, hx.active_eq]
  decide

/-- The loop condition fails after completion. -/
private theorem Done.stopped {q : ℕ} {ans : Option ℕ} {mem : ℕ → ℕ} {y : Data registers}
    (hy : Done q ans mem y) : ¬(Cond.lt zero active).Holds y := by
  simp [Cond.holds_lt, hy.zero_eq, hy.active_eq]

private theorem descent_time_le {k h : ℕ} (hk : k < h) :
    201011 + (201022 * (k + 1) + 2) + 2 ≤ 201022 * (h + 1) + 2 := by
  omega

/-- Complete loop execution from real preprocessed RAM. Every iteration costs at most
201020 instructions and there are at most `height + 1` iterations; loop tests and jumps
are charged too. The pointer may change, while all memory and the query are preserved. -/
private theorem exec_loop_height (h : ℕ) {w q p : ℕ} {t : Tree} {x : Data registers}
    (hheight_bound : t.height ≤ h) (hx : Entry q p x)
    (ht : Lean.FusionTree.Tree.Valid (branching w) t)
    (hs : t.keys.Pairwise (· < ·)) (hk : ∀ k ∈ t.keys, Fits w k)
    (hr : Rep (parameterWords w) t p x.mem) (ha : ArenaFits w p t) (hq : Fits w q) :
    ∃ y, ExecWithin w (loop w) x y (201022 * (h + 1) + 2) ∧
      Done q (t.predecessor q) x.mem y := by
  induction h using Nat.strong_induction_on generalizing t p x with
  | _ h ih =>
    let u := x.set tag (x.mem p)
    have hload : Exec (B := .standard) w (.op (.load tag pointer)) x u 1 := by
      simpa only [hx.pointer_eq] using
        (Exec.load (B := .standard) (w := w) (d := tag) (a := pointer) (x := x))
    have hu : Entry q p u := hx.set_scratch tag (by decide) (by decide) _
    cases t with
    | leaf xs =>
      have hh := hr.leaf_fields
      have htag : (Cond.eq tag zero).Holds u := by
        rw [Cond.holds_eq, hu.zero_eq]
        simp [u, hh.1]
      have hp2 : Fits w (p + 2) := ha.of_le (by simp only [span, headerWords]; omega)
      let y := leafResult u p q
      have he := exec_leaf hu hp2
      have hb : ExecWithin w (body w) x y 14 :=
        hload.within.seq (ExecWithin.branch_pos (neg := internal w) htag he)
      have hy := leafResult_spec hu
      have hans : answer y = (Lean.FusionTree.Tree.leaf xs).predecessor q := by
        have hlen : xs.length ≤ 1 := by
          simpa only [Lean.FusionTree.Tree.Valid] using ht
        cases xs with
        | nil =>
          simpa [y, u, hh.2.1, Lean.FusionTree.Tree.predecessor,
            Lean.FusionTree.Tree.listPredecessor] using hy.2.2.2.2.2
        | cons k ks =>
          have hnil : ks = [] := by simpa using hlen
          subst ks
          by_cases hlt : q < k
          · simpa [y, u, hh.2.1, hh.2.2, Lean.FusionTree.Tree.predecessor,
              Lean.FusionTree.Tree.listPredecessor, hlt, Nat.not_le.mpr hlt] using hy.2.2.2.2.2
          · simpa [y, u, hh.2.1, hh.2.2, Lean.FusionTree.Tree.predecessor,
              Lean.FusionTree.Tree.listPredecessor, hlt, Nat.le_of_not_gt hlt] using hy.2.2.2.2.2
      have hd : Done q ((Lean.FusionTree.Tree.leaf xs).predecessor q) x.mem y :=
        ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hans⟩
      exact ⟨y, (hb.loop_once hx.running hd.stopped).mono
        (by omega), hd⟩
    | node m cs =>
      have hh := hr.node_header
      have htag : ¬(Cond.eq tag zero).Holds u := by
        rw [Cond.holds_eq, hu.zero_eq]
        simp [u, hh.1]
      obtain ⟨v, hev, hvr, hvm, hv⟩ := exec_node hu ht hs hk hr ha hq
      let r := upperRank (childMinima cs) q
      have hroute := Lean.FusionTree.Tree.selectChild_eq_rank q cs (childMinima_strictMono ht hs)
      change Lean.FusionTree.Tree.selectChild q cs = (if r = 0 then none else cs[r - 1]?) at hroute
      by_cases hr0 : r = 0
      · have htest : (Cond.eq rank zero).Holds v := by
          simp only [Cond.holds_eq, hvr, hv.zero_eq]
          exact hr0
        let y := v.set active 0
        have hstop : ExecWithin (B := .standard) w (.op (.const active 0)) v y 1 :=
          ExecWithin.const (fits_zero w)
        have hint : ExecWithin w (internal w) u y 201002 :=
          hev.seq (ExecWithin.branch_pos (neg := follow) htest hstop)
        have hb : ExecWithin w (body w) x y 201005 :=
          hload.within.seq (ExecWithin.branch_neg (pos := leaf) htag hint)
        have hpred : (Lean.FusionTree.Tree.node m cs).predecessor q = none := by
          rw [Lean.FusionTree.Tree.predecessor, hroute, ite_eq_left hr0]
        have hd : Done q ((Lean.FusionTree.Tree.node m cs).predecessor q) x.mem y := by
          constructor
          · simp [y]
          · simpa +decide [y] using hv.zero_eq
          · exact hvm
          · simpa +decide [y] using hv.query_eq
          · simp +decide [y, hv.found_eq]
          · simp +decide [answer, y, hv.found_eq, hpred]
        exact ⟨y, (hb.loop_once hx.running hd.stopped).mono
          (by omega), hd⟩
      · have hrle : r ≤ cs.length := upperRank_le _ _
        let i : Fin cs.length := ⟨r - 1, by omega⟩
        have hc := hr.child i
        have hpentry : Fits w (p + 19 + 2 * (r - 1)) :=
          ha.of_le (by simp only [span, headerWords]; omega)
        have hfollow := exec_follow hv hvr hpentry
        let z := followResult v p r
        have htest : ¬(Cond.eq rank zero).Holds v := by
          simp only [Cond.holds_eq, hvr, hv.zero_eq]
          exact hr0
        have hint : ExecWithin w (internal w) u z 201008 :=
          hev.seq (ExecWithin.branch_neg (pos := .op (.const active 0)) htest hfollow.within)
        have hb : ExecWithin w (body w) x z 201011 :=
          hload.within.seq (ExecWithin.branch_neg (pos := leaf) htag hint)
        have hptr : v.mem (p + 19 + 2 * (r - 1)) = childAddress p cs i := by
          rw [hvm]
          rw [show p + 19 + 2 * (r - 1) = p + 18 + (2 * (r - 1) + 1) by omega]
          exact hc.2.1
        have hz : Entry q (childAddress p cs i) z := by
          simpa only [hptr] using (followResult_entry hv (r := r))
        have hzm : z.mem = x.mem := hvm
        have hv' := ht
        simp only [Lean.FusionTree.Tree.Valid] at hv'
        have hchild : Lean.FusionTree.Tree.Valid (branching w) cs[i] :=
          (hv'.2.2.2 _ (List.getElem_mem i.isLt)).1
        simp only [Lean.FusionTree.Tree.keys] at hs hk
        have hschild : cs[i].keys.Pairwise (· < ·) :=
          (List.pairwise_flatMap.mp hs).1 _ (List.getElem_mem i.isLt)
        have hkchild : ∀ k ∈ cs[i].keys, Fits w k := fun k hk' =>
          hk k (List.mem_flatMap.mpr ⟨cs[i], List.getElem_mem i.isLt, hk'⟩)
        have hrchild : Rep (parameterWords w) cs[i] (childAddress p cs i) z.mem := by
          simpa only [hzm] using hc.2.2
        have hheight := Tree.height_getElem_lt_node m cs i
        obtain ⟨y, hey, hy⟩ := ih cs[i].height
          (hheight.trans_le hheight_bound) le_rfl
          hz hchild hschild hkchild hrchild (ha.child i)
        have hpred : (Lean.FusionTree.Tree.node m cs).predecessor q = cs[i].predecessor q := by
          rw [Lean.FusionTree.Tree.predecessor, hroute, ite_eq_right hr0,
            List.getElem?_eq_getElem i.isLt]
          rfl
        refine ⟨y, (hb.loop_iter hx.running hey).mono ?_, ?_⟩
        · exact descent_time_le (hheight.trans_le hheight_bound)
        · simpa only [hpred, hzm] using hy

/-- The traversal bound uses the actual tree height, including the final leaf visit. -/
theorem exec_loop {w q p : ℕ} {t : Tree} {x : Data registers}
    (hx : Entry q p x) (ht : Lean.FusionTree.Tree.Valid (branching w) t)
    (hs : t.keys.Pairwise (· < ·)) (hk : ∀ k ∈ t.keys, Fits w k)
    (hr : Rep (parameterWords w) t p x.mem) (ha : ArenaFits w p t) (hq : Fits w q) :
    ∃ y, ExecWithin w (loop w) x y (201022 * (t.height + 1) + 2) ∧
      Done q (t.predecessor q) x.mem y :=
  exec_loop_height t.height le_rfl hx ht hs hk hr ha hq

end Cslib.Algorithms.WordRAM.FusionTree.QueryProgram
