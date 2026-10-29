/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PPT
import Complexity.Probability.BitString.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Logic.Relation

/-! Adaptive closed programs, invariant-based resource proofs and independent saved blocks. -/

namespace ComplexityTests.AdaptivePPT

open Cslib Cslib.Probability Turing.MultiTapeTM

example : BitString.listRows 3 2 [true, false, true] =
    [[true, false], [true, false], [false, false]] := by rfl

example : BitString.listRows 3 0 [true] = [[], [], []] := by rfl

example : BitString.listRows 0 4 [true] = [] := by rfl

-- Both dimensions are runtime values; short inputs are padded and all output cells are charged.
example : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => BitString.listRows p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) (encList encBits) := by fun_prop

-- Two independent one-bit rows disagree in this specified order with probability `1 / 4`.
example : ((BitString.uniformList 2).map (BitString.listRows 2 1))
    [[true], [false]] = 1 / 4 := by
  change ((BitString.uniformList (2 * 1)).map (BitString.listRows 2 1)) _ = _
  rw [BitString.uniformList_listRows, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have hcount : (Finset.univ.filter fun rows : Fin 2 → BitString 1 =>
      [[true], [false]] = List.ofFn (fun i => List.ofFn (rows i))).card = 1 := by decide
  rw [hcount]
  norm_num

private noncomputable def grow (state : List Bool) : ProbComp (List Bool) := do
  let bit ← ProbComp.uniform Bool
  return bit :: state

private theorem grow_ppt : IsPPTOn encBits encBits grow := by unfold grow; ppt

private theorem grow_length (state next : List Bool)
    (h : next ∈ (ProbComp.eval (grow state)).support) : next.length ≤ state.length + 1 := by
  simp only [grow, ProbComp.eval_bind, ProbComp.eval_pure] at h
  obtain ⟨bit, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  simp [← heq]

-- A full functional client certifies a quadratic number of state-dependent transitions.
example : IsPPTOn encUnary encBits (fun n => OracleComp.iterate (n * n) grow []) := by
  have hstep := grow_ppt
  have hgrowth := grow_length
  ppt

-- A polynomial iteration count alone cannot certify an exponentially growing output.
example : True := by
  fail_if_success
    have : IsPPTOn encUnary encUnary
        (fun n => OracleComp.iterate n (fun state => pure (2 * state)) n) := by ppt
  trivial

-- A small expected state size does not bound every supported execution of a strict PPT loop.
example : True := by
  fail_if_success
    have : IsPPTOn encUnary encUnary (fun n => OracleComp.iterate n (fun state => do
        let bit ← ProbComp.uniform Bool
        return if bit then 2 * state else 0) 1) := by ppt
  trivial

-- A family of separate step certificates is insufficient: captured inputs need one joint
-- machine certificate, even when the complete output size has an input-dependent growth bound.
example (step : ℕ → List Bool → ProbComp (List Bool))
    (_hpointwise : ∀ n, IsPPTOn encBits encBits (step n))
    (_hgrowth : ∀ n state next, next ∈ (ProbComp.eval (step n state)).support →
      next.length ≤ state.length + n) : True := by
  have hsize : PolyBounded (fun n => (encUnary n).length) id :=
    ComputableInPolyTime.polyBounded (by fun_prop)
  fail_if_success
    have : IsPPTOn encUnary encBits (fun n => OracleComp.iterate n (step n) []) := by ppt
  trivial

-- An implicit binary graph is supplied by an efficient transition function. The loop contract
-- certifies both its machine time and that every possible output is reachable from its input.
example (neighbor : List Bool → Bool → List Bool)
    (hefficient : ComputableInPolyTime (fun p : List Bool × Bool => neighbor p.1 p.2)
      (encPair encBits encBool) encBits)
    (hsize : ∀ state bit, (neighbor state bit).length ≤ state.length) :
    let step (state : List Bool) : ProbComp (List Bool) := do
      let bit ← ProbComp.uniform Bool
      return neighbor state bit
    IsPPTOn encBits encBits (fun start => OracleComp.iterate (start.length ^ 2) step start) ∧
      ∀ start final, final ∈
        (ProbComp.eval (OracleComp.iterate (start.length ^ 2) step start)).support →
        final.length ≤ start.length ∧
          Relation.ReflTransGen (fun a b => ∃ bit, neighbor a bit = b) start final := by
  dsimp only
  let step (state : List Bool) : ProbComp (List Bool) := do
    let bit ← ProbComp.uniform Bool
    return neighbor state bit
  have hstep : IsPPTOn encBits encBits step := by dsimp only [step]; ppt
  exact IsPPTOn.iterate_spec (by fun_prop) (by fun_prop : ComputableTidilyInPolyTime id encBits _)
    hstep
    (fun start _ state => state.length ≤ start.length ∧
      Relation.ReflTransGen (fun a b => ∃ bit, neighbor a bit = b) start state)
    (fun _ => ⟨le_rfl, .refl⟩)
    (by
      intro start i state _ hstate next hnext
      simp only [step, ProbComp.eval_bind, ProbComp.eval_pure] at hnext
      obtain ⟨bit, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      exact ⟨by simpa only [← heq] using (hsize state bit).trans hstate.1,
        hstate.2.tail ⟨bit, heq⟩⟩)
    (size := List.length) (ComputableInPolyTime.polyBounded (by fun_prop))
    (fun _ _ _ _ h => h.1)

private noncomputable def cappedStep (limit state : ℕ) : ProbComp ℕ := do
  let bit ← ProbComp.uniform Bool
  return if bit && decide (state < limit) then state + 1 else state

-- Compound guards retain ordinary functional syntax through deterministic and PPT automation.
example : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × Bool =>
      if p.2 && decide (p.1.2 < p.1.1) then p.1.2 + 1 else p.1.2)
    (encPair (encPair encUnary encUnary) encBool) encUnary := by fun_prop

example : ComputableInPolyTime
    (fun p : ℕ × ℕ => if p.1 ≤ p.2 ∧ p.2 < p.1 + 3 then p.1 + 1 else p.2)
    (encPair encUnary encUnary) encUnary := by polytime

-- Captured input affects every transition, while the invariant bounds only the changing state.
example : IsPPTOn encUnary encUnary
    (fun limit => OracleComp.iterate (limit * limit) (cappedStep limit) 0) ∧
    ∀ limit final,
      final ∈ (ProbComp.eval (OracleComp.iterate (limit * limit) (cappedStep limit) 0)).support →
      final ≤ limit := by
  have hstep : IsPPTOn (encPair encUnary encUnary) encUnary
      (fun p => cappedStep p.1 p.2) := by
    unfold cappedStep
    ppt
  exact IsPPTOn.iterateWith_spec (by fun_prop) (by fun_prop) hstep
    (fun limit _ state => state ≤ limit) (by simp)
    (by
      intro limit i state _ hstate next hnext
      simp only [cappedStep, ProbComp.eval_bind, ProbComp.eval_pure] at hnext
      obtain ⟨bit, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      split
      · next hmove =>
          have := of_decide_eq_true (Bool.and_eq_true_iff.mp hmove).2
          lia
      · exact hstate)
    (size := id) (ComputableInPolyTime.polyBounded (by fun_prop))
    (fun _ _ _ _ h => by simpa using h)

-- Zero iterations perform no transition, including for the captured-input client.
example : ProbComp.eval (OracleComp.iterate 0 (cappedStep 0) 0) = PMF.pure 0 := by simp

-- The resource bound is mathematical data; no computation certificate for it is required.
example (bound : List Bool → ℕ) (hsize : PolyBounded List.length bound)
    (hbound : ∀ word, word.length ≤ bound word) :
    IsPPTOn encBits encBits (fun word =>
      OracleComp.iterate word.length (fun state => pure state) word) := by
  refine (IsPPTOn.iterate_spec (by fun_prop) (by fun_prop) (by ppt)
    (fun word _ state => state = word) (by simp) ?_ hsize ?_).1
  · intro word i state _ hstate next hnext
    simpa [hstate] using hnext
  · intro word i state _ hstate
    simpa [hstate] using hbound word

private noncomputable def sampledRows (p : List Bool × ℕ) : ProbComp (List (List Bool)) :=
  OracleComp.iterate p.2 (fun rows => do
    let bit ← ProbComp.uniform Bool
    return (bit :: p.1) :: rows) []

-- Every sampled row copies the captured word. The invariant describes the rows; the bound
-- charges each sampled bit, copied word, and list frame, including on low-probability paths.
private theorem sampledRows_spec :
    IsPPTOn (encPair encBits encUnary) (encList encBits) sampledRows ∧
      ∀ p rows, rows ∈ (ProbComp.eval (sampledRows p)).support →
        rows.length = p.2 ∧ ∀ row ∈ rows, row.length = p.1.length + 1 := by
  unfold sampledRows
  refine IsPPTOn.iterateWith_spec ?_ ?_ ?_
    (fun (p : List Bool × ℕ) i (rows : List (List Bool)) =>
      rows.length = i ∧ ∀ row ∈ rows, row.length = p.1.length + 1)
    (by simp) ?_ (size := fun p => p.2 * (2 * (p.1.length + 1) + 1)) ?_ ?_
  · fun_prop
  · fun_prop
  · ppt
  · intro p i rows _ hrows next hnext
    simp only [ProbComp.eval_bind, ProbComp.eval_pure] at hnext
    obtain ⟨bit, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
    simpa only [List.length_cons, hrows.1, List.mem_cons, forall_eq_or_imp, true_and]
      using hrows.2
  · exact ComputableInPolyTime.polyBounded (by fun_prop)
  · intro p i rows hi hrows
    calc
      (encList encBits rows).length ≤ rows.length * (2 * (p.1.length + 1) + 1) :=
        length_encList_le encBits rows fun row hrow => by simp [hrows.2 row hrow]
      _ ≤ _ := by simpa only [hrows.1] using Nat.mul_le_mul_right _ hi

-- The certified loop composes with an ordinary functional scan of the accumulated rows.
example : IsPPTOn (encPair encBits encUnary) encBool (fun p => do
    let rows ← sampledRows p
    return rows.any (fun row => row.all id)) := by
  have hrows := sampledRows_spec.1
  ppt

example : ProbComp.eval (sampledRows ([true, false], 0)) = PMF.pure [] := by
  simp [sampledRows]

end ComplexityTests.AdaptivePPT
