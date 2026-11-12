/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Interactive.Security.Oracle
import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import CslibFrontier.Foundations.Control.Monad.Memoize

/-!
# Adaptive stateful replacement with uncharged cache operations

Two signing calls are separated by repeated hash reads whose key depends on the first reply.
The state retains both the memoized answers and the repeated signing log. Only signing costs
error; the shared hash handler may extend the cache even though its cost is zero.
-/

namespace CslibFrontierTests.OracleStatistical

open Cslib Cslib.OracleComp Cslib.Interactive Cslib.Probability
open scoped ENNReal NNReal Cslib.Probability.PMF

private abbrev Store := List (Bool × Bool) × List Bool

private def signingCost : Bool ⊕ Bool → ℕ
  | .inl _ => 1
  | .inr _ => 0

private noncomputable def handler (μ : PMF Bool) :
    (q : Bool ⊕ Bool) → StateT Store PMF Bool
  | .inl msg, s => μ.map fun b => (b, (s.1, msg :: s.2))
  | .inr key, s => (memoize (fun b => PMF.pure b) key s.1).map
      fun out => (out.1, (out.2, s.2))

private def adaptive : OracleComp (fun _ : Bool ⊕ Bool => Bool) Bool := do
  let a ← query (.inl false)
  let h ← query (.inr a)
  let h' ← query (.inr a)
  let b ← query (.inl false)
  return a && b && (h == h')

private theorem adaptive_bounded : IsCostBounded signingCost adaptive 2 := by
  unfold adaptive
  refine IsCostBounded.liftBind (cost := signingCost) (Sum.inl false) _ 1 fun a => ?_
  refine IsCostBounded.liftBind (cost := signingCost) (Sum.inr a) _ 1 fun h => ?_
  refine IsCostBounded.liftBind (cost := signingCost) (Sum.inr a) _ 1 fun h' => ?_
  exact IsCostBounded.liftBind (cost := signingCost) (Sum.inl false) _ 0 fun b =>
    IsCostBounded.pure _ 0

-- Every starting cache/log is covered, not just the empty state.
private theorem close_adaptive {μ ν : PMF Bool} {ε : ℝ≥0∞} (h : CloseTo μ ν ε) (s : Store) :
    CloseTo (runWith (handler μ) adaptive s) (runWith (handler ν) adaptive s) (2 * ε) := by
  apply adaptive_bounded.closeTo_runWith
  intro q st
  cases q with
  | inl msg =>
    simpa only [handler, signingCost, Nat.cast_one, one_mul] using
      h.map (fun b => (b, (st.1, msg :: st.2)))
  | inr key => simpa only [handler, signingCost, Nat.cast_zero, zero_mul] using
      CloseTo.refl ((handler μ) (.inr key) st)

-- Repeated reads cache one point, while repeated signing messages remain in the log.
example : runWith (handler (PMF.pure true)) adaptive ([], []) =
    PMF.pure (true, ([(true, true)], [false, false])) := by
  simp [adaptive, handler, memoize]

private noncomputable def biased : PMF Bool :=
  PMF.ofFintype (fun b => cond b (3 / 4) (1 / 4)) (by
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    rw [ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by finiteness))

private theorem pure_close_biased : CloseTo (PMF.pure true) biased (1 / 4) := by
  have h : dist (PMF.pure true) biased ≤ (1 / 4 : ℝ≥0) := by
    norm_num [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, PMF.pure_apply,
      biased, PMF.ofFintype_apply]
  simpa using closeTo_of_dist_le h

-- A concrete nonzero replacement error gives a nontrivial bound on joint output/cache/log.
example : CloseTo (runWith (handler (PMF.pure true)) adaptive ([], []))
    (runWith (handler biased) adaptive ([], [])) (1 / 2) := by
  have h := close_adaptive pure_close_biased ([], [])
  convert h using 1
  rw [← ENNReal.coe_ofNat 2, ← ENNReal.coe_ofNat 4, ← ENNReal.coe_one,
    ← ENNReal.coe_div (by norm_num), ← ENNReal.coe_div (by norm_num), ← ENNReal.coe_mul]
  norm_num

-- Zero budget remains zero even at infinite per-unit error; state mutation is retained.
example (s : ℕ) :
    CloseTo
      (runWith (fun (_ : Unit) s => PMF.pure (true, s + 1)) (query ()) s)
      (PMF.pure (true, s + 1)) 0 := by
  have hb := IsCostBounded.query (spec := fun _ : Unit => Bool) (cost := fun _ => 0) ()
  have h := hb.closeTo_runWith (left := fun _ s => PMF.pure (true, s + 1))
      (right := fun _ s => PMF.pure (true, s + 1)) (ε := ⊤)
      (fun _ _ => by simp) s
  simpa only [Nat.cast_zero, zero_mul, runWith_query] using h

-- Equal replies alone do not justify zero-cost replacement when the state updates differ.
example : ¬ CloseTo (PMF.pure (true, (1 : ℕ))) (PMF.pure (true, (0 : ℕ))) 0 := by
  intro h
  have hs := h {(true, 1)}
  simp [PMF.toOuterMeasure_apply_singleton, PMF.pure_apply] at hs

end CslibFrontierTests.OracleStatistical
