/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.State
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Expand
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.FullLeaf

/-!
# Complete charged native frontier step

The real pop, branch, child stores and signed leaf consumption preserve the finite
frontier invariant and decrease a measure recovered from actual memory. Original
array magnitudes and original address arguments derive every intermediate fit.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Execute one complete real frontier iteration, without a runtime or timing oracle. -/
theorem exec_step {w L m t AA BB D V K F A B : ℕ} (x : Data registers)
    (η : OutStr L) (hη : (innerSetO η).card = m) (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (finished : List (Leaf L)) (xs : List Term) (rest : List (List Term))
    (hx : Ready η m t AA BB D V K F a b finished (xs :: rest) x)
    (hK : K = (boxes L m t).card) (hF : F = V + K)
    (hAA : AA + 10 ^ L ≤ F) (hBB : BB + 10 ^ L ≤ F)
    (hD : D + (m - t + 1) * 10 ^ L ≤ F)
    (hfit : Fits (w + 2) (queryAddressBound L t AA BB D V K))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    ∃ y finished' tasks', ExecWithin (w + 2) body x y 256 ∧
      Ready η m t AA BB D V K F a b finished' tasks' y ∧
      workMeasure η t F y < workMeasure η t F x ∧
      (∀ q, ¬(F ≤ q ∧ q < F + 5 * stackCapacity L) → y.mem q = x.mem q) := by
  have hp := hx.parameters
  have hxs : Good η t xs := hx.frontier.good xs (by simp)
  have hpending := hx.pending_le hη
  simp only [List.length_cons] at hpending
  have hTpos : 0 < 10 ^ L := by positivity
  have hL : L ≤ (L + 1) * 10 ^ L := (Nat.le_succ L).trans
    (Nat.le_mul_of_pos_right _ hTpos)
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  have hquery := (PrunedQuery.queryIndex η).isLt
  have hVK : V + (boxes L m t).card ≤ F := by rw [← hK]; omega
  obtain ⟨htask, hrest⟩ := hx.stack.pop
  obtain ⟨u, hu, un, uk, uc, uu, ue, upow, um, uf⟩ := exec_pop
    (F := F) (n := rest.length) x hp.stack (by simpa only [List.length_cons] using hx.top)
    hp.five hp.one htask.depth htask.code htask.used htask.stars htask.power
    (hfit.of_le (by unfold queryAddressBound; omega))
  have up := hp.after_pop hu
  have ustack : StackMemory η F rest u.mem := by simpa only [um] using hrest
  have utable : Readback m t D V AA BB a b u.mem := by simpa only [um] using hx.table
  have uanswer : u.regs Reg.answer = Signed.encode
      ((finished.map (leafQueryValue m t η a b)).sum) :=
    (uf _ (by decide)).trans hx.answer
  by_cases hk : xs.length < L
  · have hpowle : 10 ^ (xs.length + 1) ≤ 10 ^ L :=
      Nat.pow_le_pow_right (by decide) (by omega)
    obtain ⟨y, hy, yn, ystack, yframe, yf⟩ := exec_expand η xs rest u hxs hk ustack
      up.stack un up.query up.threshold uk uc uu ue upow up.five up.one up.ten up.nine up.nil
      (hfit.of_le (by unfold queryAddressBound; omega))
    have he : ExecWithin (w + 2) body x y 256 :=
      (hu.seq (hy.branch_pos (by simpa only [Cond.holds_lt, uk, up.levels] using hk))).mono
        (by omega)
    have hframe (q : ℕ) (hq : ¬(F ≤ q ∧ q < F + 5 * stackCapacity L)) :
        y.mem q = x.mem q := by
      rw [yframe q (by
        have hc := children_length_le η t xs
        unfold stackCapacity at hq
        omega), um]
    have hready : Ready η m t AA BB D V K F a b finished
        (children η t xs ++ rest) y := by
      refine ⟨hp.after_body he, hx.frontier.expand hk, ?_, ystack, ?_, ?_⟩
      · simpa only [List.length_append, Nat.add_comm] using yn
      · exact (yf _ (by decide)).trans uanswer
      · exact hx.table.transport hAA hBB hD hVK (fun q hq => hframe q (by omega))
    refine ⟨y, finished, children η t xs ++ rest, he, hready, ?_, hframe⟩
    rw [hready.work_eq, hx.work_eq]
    exact frontierWork_expand_lt hxs hk rest
  · have hlen : xs.length = L := by have := hxs.1; omega
    let τ := completeLeaf xs hlen
    let z := (finished.map (leafQueryValue m t η a b)).sum
    obtain ⟨y, hy, yanswer, ym, yf⟩ := exec_fullLeaf u η hη xs hxs hlen a b ha hb up uc uu ue
      utable z uanswer (hx.answer_natAbs_le hη ha hb)
      (hfit.of_le (by unfold queryAddressBound; omega)) hmag
    have he : ExecWithin (w + 2) body x y 256 :=
      (hu.seq (hy.branch_neg (by simpa only [Cond.holds_lt, uk, up.levels] using hk))).mono
        (by omega)
    have hyμ : y.mem = x.mem := ym.trans um
    have hτ : Good η t (List.ofFn τ) := by simpa only [τ, ofFn_completeLeaf] using hxs
    have hfront : FrontierInvariant η t (leafQueryValue m t η a b)
        (finished ++ [τ]) rest := by
      have hf : FrontierInvariant η t (leafQueryValue m t η a b) finished
          (List.ofFn τ :: rest) := by simpa only [τ, ofFn_completeLeaf] using hx.frontier
      exact hf.finish
    have hready : Ready η m t AA BB D V K F a b (finished ++ [τ]) rest y := by
      refine ⟨hp.after_body he, hfront, ?_, ?_, ?_, ?_⟩
      · exact (yf _ (by decide)).trans un
      · simpa only [ym] using ustack
      · simpa only [List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton, τ, z] using yanswer
      · simpa only [hyμ] using hx.table
    refine ⟨y, finished ++ [τ], rest, he, hready, ?_, fun q _ => congrFun hyμ q⟩
    rw [hready.work_eq, hx.work_eq]
    have hwork := frontierWork_finish τ hτ rest
    rw [ofFn_completeLeaf] at hwork
    omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
