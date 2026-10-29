/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ProgressChild
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ProgressEmpty
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ProgressFinish
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ProgressReturn

/-!
# All-depth execution of the native pruned controller

## Main results

* `PrunedQuery.exec_ready`: the fixed controller computes the existing pruned recursion, with
  actual stored child lists, signed values, frames and a bound charged to its mathematical trace.

The induction composes only `Code.ExecWithin` for the existing standard unsigned machine. Its
continuation form stops the inductive node at the parent return cursor; at the root the proved
zero active flag supplies the ordinary native loop-exit execution.
The stage execution lemmas and node invariants here are internal implementation APIs,
exported for proof composition across modules. Callers use `Pruned.Kernel` or `Pruned.Flat`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- An arbitrary-depth ready node returns the unchanged finite pruned result. The only width
premises concern original pointers, depths, epochs and input magnitudes; all intermediate fits
are derived. Every child is generated and executed by the same fixed native controller. -/
theorem exec_ready {w L f a0 b0 A B : ℕ} (n : ℕ) {d p E : ℕ}
    (S : Finset (OutStr n)) (a b : Leaf n → ℤ) (x : Data registers)
    (hx : NodeReady L f a0 b0 n d p E S x)
    (hleft : ∀ v, x.mem (a0 + p + 10 ^ d * (Encoding.leafIndex v).val) = encode (a v))
    (hright : ∀ v, x.mem (b0 + p + 10 ^ d * (Encoding.leafIndex v).val) = encode (b v))
    (hbeforeA : a0 + 10 ^ L ≤ f) (hbeforeB : b0 + 10 ^ L ≤ f)
    (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hw : 0 < w) (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (nodeBudget L f a0 b0 E n)) :
    ∃ y, NodeResult L f a0 b0 n d E S a b x y ∧
      ∀ z U, ExecWithin (w + 2) controller y z U →
        ExecWithin (w + 2) controller x z (traceWeight S + U) := by
  induction n generalizing d p E x with
  | zero => exact exec_ready_zero S a b x hx hleft hright ha hb hw hmag hfit
  | succ n ih =>
    obtain ⟨y, henter, hy⟩ := exec_ready_enter S a b x hx hfit
    have hterms : ∀ k ≤ 10, ∃ u, NodeProgress L f a0 b0 n d p E S a b x k u ∧
        ∀ z U, ExecWithin (w + 2) controller u z U →
          ExecWithin (w + 2) controller y z
            (k * (51 * S.card + 75) + childWeightPrefix S k + U) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨y, hy, ?_⟩
        intro z U hz
        simpa only [Nat.zero_mul, childWeightPrefix_zero, Nat.zero_add] using hz
      | succ k ihk =>
        intro hk
        obtain ⟨u, hu, hprevious⟩ := ihk (by omega)
        let t : Fin 10 := ⟨k, by omega⟩
        by_cases hne : (childSet S (Encoding.termDigits t)).Nonempty
        · obtain ⟨v, hpush, hv, hpushFrame, hvfit⟩ := exec_progress_child S a b x u hx t hu hne hfit
          obtain ⟨z, hz, hchild⟩ := ih (childSet S (Encoding.termDigits t))
            (sliceAt a (Encoding.termDigits t)) (sliceAt b (Encoding.termDigits t)) v hv
            (hu.child_source hx t hpushFrame hbeforeA hleft)
            (hu.child_source hx t hpushFrame hbeforeB hright)
            (fun v => ha (Fin.cons (Encoding.termDigits t) v))
            (fun v => hb (Fin.cons (Encoding.termDigits t) v)) hvfit
          obtain ⟨v', hreturn, hv'⟩ := exec_progress_return S a b x u v z hx t hu hne
            hpushFrame hz ha hb hw hmag hfit
          refine ⟨v', hv', ?_⟩
          intro endState U hend
          have hza : z.regs active = 1 := by
            simpa only [ite_eq_right (by omega : d + 1 ≠ 0)] using hz.active_eq
          have hreturnLoop := ExecWithin.loop_iter
            (by simp only [Cond.holds_lt, hz.regs.nil_eq, hza]; decide) hreturn hend
          have hchildLoop := hchild endState _ hreturnLoop
          have hpushLoop := ExecWithin.loop_iter
            (by simp only [Cond.holds_lt, hu.regs.nil_eq, hu.active_eq]; decide) hpush hchildLoop
          have he := hprevious endState _ hpushLoop
          apply he.mono
          have hweight := childWeightPrefix_succ S t
          simp only [hne, ↓reduceIte] at hweight
          change childWeightPrefix S (k + 1) = childWeightPrefix S k +
            traceWeight (childSet S (Encoding.termDigits t)) at hweight
          simp only [Nat.add_mul, Nat.one_mul]
          omega
        · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
          obtain ⟨v, hskip, hv⟩ := exec_progress_empty S a b x u hx t hu hempty hfit
          refine ⟨v, hv, ?_⟩
          intro endState U hend
          have hskipLoop := ExecWithin.loop_iter
            (by simp only [Cond.holds_lt, hu.regs.nil_eq, hu.active_eq]; decide) hskip hend
          have he := hprevious endState _ hskipLoop
          apply he.mono
          have hweight := childWeightPrefix_succ S t
          simp only [hne, ↓reduceIte, Nat.add_zero] at hweight
          change childWeightPrefix S (k + 1) = childWeightPrefix S k at hweight
          simp only [Nat.add_mul, Nat.one_mul]
          omega
    obtain ⟨u, hu, hchildren⟩ := hterms 10 (by omega)
    obtain ⟨z, hfinish, hz⟩ := exec_progress_finish S a b x u hx hu hfit
    refine ⟨z, hz, ?_⟩
    intro endState U hend
    have hfinishLoop := ExecWithin.loop_iter
      (by simp only [Cond.holds_lt, hu.regs.nil_eq, hu.active_eq]; decide) hfinish hend
    have hchildrenLoop := hchildren endState _ hfinishLoop
    have he := ExecWithin.loop_iter
      (by simp only [Cond.holds_lt, hx.regs.nil_eq, hx.active_eq]; decide) henter hchildrenLoop
    apply he.mono
    rw [traceWeight_succ_prefix]
    have hc := node_local_cost_le S.card
    omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
