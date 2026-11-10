/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
public import CslibFrontier.Computability.GenericRAM.Native.Combinators
-- Reuse the normalized-tree correspondence and size lemmas without exporting its private model.
import all CslibFrontier.Computability.Complexity.FineGrained.Sparsification
import Mathlib.Data.List.Fold

/-!
# Materializing the sparsification leaves

The executable collector uses the same computed branching steps and binary round count as the
Boolean sparsification search, but returns its leaves, in reverse visitation order. Distinct
branch words are retained even when their formulas coincide: the length bound counts these
multiplicities. No satisfiability oracle is executed by the collector.

`certificate` charges actual trajectory maxima, including the growing output accumulator. Its
bounds are not a proof of the sharp sparsification generation time: applying a polynomial step
bound to that accumulator can increase the exponential rate.

## Main definitions

* `Cslib.Complexity.Sparsify.Family.step`: the stack/output transition.
* `Cslib.Complexity.Sparsify.Family.collect`: the materialized list of leaves.
* `Cslib.Complexity.Sparsify.Family.certificate`: the native counted-loop implementation.

## Main results

* `Cslib.Complexity.Sparsify.Family.collect_any`: every Boolean leaf test agrees with the search.
* `Cslib.Complexity.Sparsify.Family.collect_length_le`: multiplicities obey the leaf bound.
* `Cslib.Complexity.Sparsify.Family.satisfiable_iff`: disjunctive correctness.
-/

public section
namespace Cslib.Complexity.Sparsify.Family

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM
open ClauseSet.Sparsification (threshold base one_le_threshold BranchingRule)
open Cslib.GenericRAM

/-- A pending stack paired with the collected leaves. -/
abbrev State := List (CNF ℕ) × List (CNF ℕ)

/-- Two lists of framed CNFs; the stack (first list) is framed, the output list is unframed. -/
abbrev encState : State ↪ List Bool := encPair (encList encCNF) (encList encCNF)

/-- Pop and emit sparse heads, or replace an inner head by its two computed children. -/
@[expose] def step (K α : ℕ) (s : State) : State :=
  if s.1.isEmpty then s
  else if isSparse (threshold K α) K (s.1.headD []) then
    (s.1.tail, s.1.headD [] :: s.2)
  else (next (threshold K α) K (s.1.headD []) false ::
    next (threshold K α) K (s.1.headD []) true :: s.1.tail, s.2)

/-- Collect the leaves, with multiplicity, by a fixed counted loop. -/
@[expose] def collect (K α k M : ℕ) (φ : CNF ℕ) : List (CNF ℕ) :=
  ((step K α)^[rounds M φ] ([root k φ], [])).2

private theorem any_step (K α : ℕ) (g : CNF ℕ → Bool) (s : State) :
    (step K α s).map id (List.any · g) =
      Sparsify.step K α g (s.1, s.2.any g) := by
  rcases s with ⟨stk, acc⟩
  simp only [step, Sparsify.step]
  split_ifs <;> simp [Bool.or_comm]

/-- Testing any returned leaf agrees with the existing Boolean search, for every test. -/
theorem collect_any (K α k M : ℕ) (g : CNF ℕ → Bool) (φ : CNF ℕ) :
    (collect K α k M φ).any g = search K α k M g φ := by
  have h (n : ℕ) (s : State) :
      ((step K α)^[n] s).map id (List.any · g) =
        (Sparsify.step K α g)^[n] (s.1, s.2.any g) := by
    induction n generalizing s with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      change (Sparsify.step K α g)^[n] ((step K α s).map id (List.any · g)) = _
      rw [any_step, Function.iterate_succ_apply]
  exact congrArg Prod.snd (h (rounds M φ) ([root k φ], []))

variable {K α : ℕ} (hK : 1 ≤ K) (hα : 1 ≤ α)

private theorem step_map (stk : List {ψ : CNF ℕ // Normalized K ψ}) (acc : List (CNF ℕ)) :
    step K α (stk.map Subtype.val, acc) =
      Prod.map (List.map Subtype.val) id
        ((rule hK hα).tree.searchStep (fun acc t => t.1 :: acc) (stk, acc)) := by
  cases stk with
  | nil => rfl
  | cons s rest =>
    have hiff := isSparse_eq_true_iff (one_le_threshold hK hα) s.2
    by_cases hs : ClauseSet.Sparsification.Sparse (threshold K α) s.1.toClauseSet
    · have hs' := hiff.mpr hs
      simp [step, BinaryBranching.searchStep, hs, hs', CNF.Sparsification.rule]
    · have hs' : isSparse (threshold K α) K s.1 = false := by
        simpa using fun h => hs (hiff.mp h)
      simp [step, BinaryBranching.searchStep, hs, hs', rule, CNF.Sparsification.rule]

private theorem iterate_step_map (n : ℕ) (stk : List {ψ : CNF ℕ // Normalized K ψ})
    (acc : List (CNF ℕ)) :
    (step K α)^[n] (stk.map Subtype.val, acc) =
      Prod.map (List.map Subtype.val) id
        (((rule hK hα).tree.searchStep (fun acc t => t.1 :: acc))^[n] (stk, acc)) := by
  induction n generalizing stk acc with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step_map hK hα]
    obtain ⟨stk', acc'⟩ := (rule hK hα).tree.searchStep (fun acc t => t.1 :: acc) (stk, acc)
    exact ih stk' acc'

include hK hα in
/-- The returned formulas are exactly the leaves, counted once for each distinct branch word. -/
private theorem collect_spec {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M) (φ : CNF ℕ) :
    ∃ L : List (List Bool), L.Nodup ∧
      (∀ w, w ∈ L ↔ (rule hK hα).tree.IsLeafWord (rootState hkK φ) w) ∧
      collect K α k M φ =
        (L.map fun w => ((rule hK hα).tree.walk (rootState hkK φ) w).1).reverse := by
  classical
  set R := rule hK hα
  set s₀ := rootState hkK φ
  have hlen : ∀ w, R.tree.IsLeafWord s₀ w → w.length ≤
      φ.numVars * (K * base K α ^ (2 * K)) :=
    fun w hw => BranchingRule.length_le_of_isLeafWord hK hα s₀.2.reduced s₀.2.card_le
      φ.vars.toFinset mem_vars_of_mem_root hw
  obtain ⟨L, hnd, hL, N, hN, h⟩ := R.tree.exists_iterate_searchStep
    (BranchingRule.tree_terminating (one_le_threshold hK hα))
    (fun acc t => t.1 :: acc) s₀ hlen
  have hLcard : L.length ≤ 2 ^ (φ.numVars / M + 1) := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact (BranchingRule.card_le_of_isLeafWord hK hα s₀.2.reduced s₀.2.card_le
      φ.vars.toFinset mem_vars_of_mem_root L.toFinset
      fun w hw => (hL w).mp (List.mem_toFinset.mp hw)).trans (hM φ.numVars)
  have hNr : N ≤ rounds M φ := by grind [rounds, CNF.length_distinctVars, pow_succ]
  obtain ⟨hfin, -⟩ := h [] []
  have hfold : (L.map (R.tree.walk s₀)).foldl (fun acc t => t.1 :: acc) [] =
      (L.map fun w => (R.tree.walk s₀ w).1).reverse := by
    simpa only [List.foldl_map, flip] using
      (List.foldl_cons_nil (l := L.map fun w => (R.tree.walk s₀ w).1))
  have hN' : (step K α)^[N] ([root k φ], []) =
      ([], (L.map fun w => (R.tree.walk s₀ w).1).reverse) := by
    change (step K α)^[N] ([s₀].map Subtype.val, []) = _
    rw [iterate_step_map hK hα, hfin, hfold]
    rfl
  refine ⟨L, hnd, hL, ?_⟩
  unfold collect
  rw [show rounds M φ = (rounds M φ - N) + N by omega, Function.iterate_add_apply, hN']
  have hnil (n : ℕ) (acc : List (CNF ℕ)) : (step K α)^[n] ([], acc) = ([], acc) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply]; exact ih
  rw [hnil]

include hK hα in
/-- The actual output length is bounded by the binomial leaf count, including repeated formulas. -/
theorem collect_length_le {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M) (φ : CNF ℕ) :
    (collect K α k M φ).length ≤
      ∑ j ∈ Finset.range ((K - 1) * φ.numVars / α + 1),
        (φ.numVars * (K * base K α ^ (2 * K))).choose j := by
  obtain ⟨L, hnd, hL, heq⟩ := collect_spec hK hα hkK hM φ
  rw [heq, List.length_reverse, List.length_map, ← List.toFinset_card_of_nodup hnd]
  exact BranchingRule.card_le_of_isLeafWord hK hα (rootState hkK φ).2.reduced
    (rootState hkK φ).2.card_le φ.vars.toFinset mem_vars_of_mem_root L.toFinset
    fun w hw => (hL w).mp (List.mem_toFinset.mp hw)

include hK hα in
/-- Collected formulas preserve width and variables and have the derived sparse clause bound. -/
theorem collect_properties {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M)
    {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) {ψ : CNF ℕ}
    (hψ : ψ ∈ collect K α k M φ) :
    (∀ c ∈ ψ, c.length ≤ k) ∧ ψ.length ≤ occBound K α * φ.numVars + 1 ∧
      ψ.numVars ≤ φ.numVars := by
  obtain ⟨L, -, hL, heq⟩ := collect_spec hK hα hkK hM φ
  rw [heq, List.mem_reverse, List.mem_map] at hψ
  obtain ⟨w, hw, rfl⟩ := hψ
  have hw' := (hL w).mp hw
  refine ⟨fun c hc => length_le_of_mem_walk hK hα hkK hφ hw'.isNodeWord hc, ?_, ?_⟩
  · exact length_walk_le_of_isSparse hK hα hkK hw'.isNodeWord
      ((isSparse_eq_true_iff (one_le_threshold hK hα)
        ((rule hK hα).tree.walk (rootState hkK φ) w).2).mpr hw'.isLeaf_walk)
  · apply Finset.card_le_card
    intro v hv
    obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
    obtain ⟨d, hd, hcd⟩ := exists_of_mem_walk hK hα hkK hw'.isNodeWord hc
    exact List.mem_toFinset.mpr (CNF.mem_vars.mpr
      ⟨d, hd, b, List.mem_toFinset.mp (hcd (List.mem_toFinset.mpr hb))⟩)

include hK hα in
/-- A valid input is satisfiable exactly when one of its actually collected leaves is. -/
theorem satisfiable_iff {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M)
    {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    φ.Satisfiable ↔ ∃ ψ ∈ collect K α k M φ, ψ.Satisfiable := by
  classical
  rw [← search_eq_true_iff hK hα hkK hM (g := fun ψ => decide ψ.Satisfiable)
    (fun _ _ => decide_eq_true_iff) hφ, ← collect_any, List.any_eq_true]
  simp only [decide_eq_true_eq]

/-- The collector transition is a native polynomial-time function of its entire encoded state.
This charges copying the accumulated output, rather than treating it as a free callback frame. -/
theorem step_polyTime (K α : ℕ) : ComputableInPolyTime (step K α) encState encState := by
  have hs := computableInPolyTime_isSparse encNat
    (ClauseSet.Sparsification.computableInPolyTime_threshold_le K α) K
  have hn := computableInPolyTime_next encNat
    (ClauseSet.Sparsification.computableInPolyTime_threshold_le K α) K
  unfold step encState encCNF
  fun_prop

/-- Native initialization, including the computed normalization of the original formula. -/
theorem init_polyTime (k : ℕ) :
    ComputableInPolyTime (fun φ : CNF ℕ => (([root k φ], []) : State)) encCNF encState := by
  have hn := computableInPolyTime_normalize encNat
  unfold root encState encCNF
  fun_prop

/-- One finite native machine collects the family, with actual loop clocks, state copies and
output storage charged by the existing counted-loop certificate. No sharp exponent is asserted. -/
noncomputable def certificate (K α k M : ℕ) :
    NativeCertificate (collect K α k M) encCNF (encList encCNF) :=
  (NativeCertificate.iterate (.ofPolyTime (computableInPolyTime_rounds M))
      (.ofPolyTime (init_polyTime k)) (.ofPolyTime (step_polyTime K α))).snd

end Cslib.Complexity.Sparsify.Family
