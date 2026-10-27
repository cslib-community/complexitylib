/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

import all CountingNativeEndpointPrep
import all CountingNativeEndpointConsequencesPrep
import all Complexity.Computability.Complexity.FineGrained.CountingNativeScalePrep
import Complexity.Computability.PolyTime.CNF.BranchedSparseCNFCounter

/-!
# Private assembly of the declared counting contract

Unaggregated author preparation for #1226. This joins the unchanged uniform search resource
supplier, Anton Kovsharov's normalized branched sparse leaf interface, and the all-input clamped
round estimate. The existing leaf schedule, original external encoding, selected input guard,
and independent time and workspace are retained. Every declaration is private.

The last theorem still assumes a concrete branch evaluator's exactness, native certificate,
global polynomial workspace, and `BranchPolylogTimeBound`. It is not an unconditional endpoint.
The bounded-incidence implementation and discharge of those premises remain with their author.
-/

namespace Cslib.Complexity.CountingNativeEndpointPrep

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.CNF.Sparsification
open Cslib.Logic.PL.ClauseSet.Sparsification Turing.MultiTapeTM Cslib.GenericRAM
open Turing.MultiTapeTM.Universal (encUnit encUnit_apply)
open CountingSparsify SubexponentialSAT SubexponentialSAT.SparsePolyCounter
open BranchedSparseCNFCounter

private abbrev LeafInput := Context × CNF ℕ
private abbrev encLeafInput := encPair encContext encCNF

/-- The prefix-size charge includes the original declared unary size and retained Unit context. -/
private def leafSize (k : ℕ) (x : FullInput) : ℕ :=
  2 * x.2.1 + 3 + nodeBound (width k) (depthCoeff k (x.1, x.2.1)) x.2.2

private theorem polyBounded_leafSize (k : ℕ) :
    PolyBounded (fun x : FullInput => (encFullInput x).length) (leafSize k) := by
  have hN : PolyBounded (fun x : FullInput => (encFullInput x).length) (fun x => x.2.1) :=
    PolyBounded.self.mono fun x => by
      simp only [encFullInput, encInput, length_encPair, encUnary_apply, List.length_replicate]
      omega
  have hL : PolyBounded (fun x : FullInput => (encFullInput x).length)
      (fun x => (encCNF x.2.2).length) :=
    PolyBounded.self.mono fun x =>
      (length_le_encPair_right encUnary encCNF x.2).trans
        (length_le_encPair_right encUnit encInput x)
  have hn := hL.mono fun x => x.2.2.numVars_le_length_vars.trans (SAT.length_vars_le x.2.2)
  have hm := hL.mono fun x => length_le_length_encList _ x.2.2
  have hnode := ((hm.add (.const 1)).add
    ((PolyBounded.const (width k)).mul ((polyBounded_depthCoeff_full k).mul hn))).mul
    (((PolyBounded.const 2).mul ((PolyBounded.const (width k)).mul
      (((PolyBounded.const 2).mul hL).add (.const 1)))).add (.const 1))
  exact (((PolyBounded.const 2).mul hN).add (.const 3)).add hnode

/-- Every active prefix, including the terminal prefix, meets the exact supplier clause cap. -/
private theorem prefix_leaf_bounds (k : ℕ) (g : LeafInput → ℕ) (x : FullInput)
    (hx : validDeclaredInput k x.2.1 x.2.2 = true) (i : ℕ)
    (hactive : let p := (x.1, x.2.1)
      let st := (step (thresholdBase k p) (width k) (fun ψ => g (p, ψ)))^[i] (init k x.2.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (thresholdBase k p)) (width k)
        (st.2.1.headD []) = true) :
    let p := (x.1, x.2.1)
    let ψ := ((step (thresholdBase k p) (width k) (fun ψ => g (p, ψ)))^[i]
      (init k x.2.2)).2.1.headD []
    ψ.length ≤ leafOccBound k x.2.1 * x.2.1 + 1 ∧
      (encLeafInput (p, ψ)).length ≤ leafSize k x := by
  have hb := (iterate_step_prefix_bounds
    ((by decide : 1 ≤ 2).trans (two_le_thresholdBase k (x.1, x.2.1)))
    ((by decide : 1 ≤ 2).trans (two_le_width k))
    (two_le_thresholdBase k (x.1, x.2.1)) (le_width k) (treeBound k (x.1, x.2.1))
    (fun ψ => g ((x.1, x.2.1), ψ)) x.2.2 i).2.2.2 hactive
  have hn := numVars_le_of_valid (x := x.2) hx
  refine ⟨?_, ?_⟩
  · rw [leafOccBound_eq_occBound]
    exact hb.2.2.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) 1)
  · simp only [encLeafInput, encContext, length_encPair, encUnit_apply,
      List.length_nil, encUnary_apply, List.length_replicate, leafSize]
    have := hb.2.2.2.2
    omega

/-- The polynomial part of the selected search cost and the ceiled leaf envelope combine with
one fixed all-input round estimate. Small declared sizes are already absorbed in that estimate. -/
private theorem selected_time_envelope (k d c e Cₜ dₜ Aₜ : ℕ) :
    let U (x : FullInput) := Cₜ * (leafSize k x + 1) ^ dₜ
    let R (x : FullInput) := ⌈(U x : ℝ) * (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.2.1)⌉₊
    let W (x : FullInput) := c * ((encFullInput x).length + 1) ^ e
    ∃ C E : ℕ, ∀ x : Input,
      (((inputSize x + 1) ^ d + if validDeclaredInput k x.1 x.2 then
        W (prepare x) + (rounds (divisor ((), x.1)) x.2 + 1) *
          (W (prepare x) + R (prepare x)) else inputSize x : ℕ) : ℝ) ≤
        C * ((2 : ℝ) ^ (((Aₜ + 16 : ℕ) : ℝ) * interpolationScale x.1) *
          ((inputSize x : ℝ) + 1) ^ E) + C := by
  dsimp only
  let U (x : FullInput) := Cₜ * (leafSize k x + 1) ^ dₜ
  let R (x : FullInput) := ⌈(U x : ℝ) * (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.2.1)⌉₊
  let W (x : FullInput) := c * ((encFullInput x).length + 1) ^ e
  let P (x : Input) := (inputSize x + 1) ^ d + W (prepare x) + U (prepare x) + 1 + inputSize x
  have hW : PolyBounded (fun x : FullInput => (encFullInput x).length) W :=
    (PolyBounded.const c).mul ((PolyBounded.self.add (.const 1)).pow e)
  have hU : PolyBounded (fun x : FullInput => (encFullInput x).length) U :=
    (PolyBounded.const Cₜ).mul (((polyBounded_leafSize k).add (.const 1)).pow dₜ)
  have hP : PolyBounded inputSize P :=
    (((((PolyBounded.self.add (.const 1)).pow d).add
      (hW.comp computableInPolyTime_prepare.polyBounded_length)).add
      (hU.comp computableInPolyTime_prepare.polyBounded_length)).add (.const 1)).add PolyBounded.self
  obtain ⟨Cₚ, E, hP⟩ := hP.exists_le
  obtain ⟨Cq, _, hq⟩ := exists_clamped_rounds_le_interpolationScale
  refine ⟨(Cq + 1) * Cₚ, E, fun x => ?_⟩
  let X : ℝ := (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.1)
  let Y : ℝ := (2 : ℝ) ^ (16 * interpolationScale x.1)
  let p : ℝ := Cₚ * ((inputSize x : ℝ) + 1) ^ E
  have hX : 1 ≤ X := Real.one_le_rpow one_le_two
    (mul_nonneg (Nat.cast_nonneg Aₜ) (interpolationScale_nonneg _))
  have hY : 1 ≤ Y := Real.one_le_rpow one_le_two
    (mul_nonneg (by norm_num) (interpolationScale_nonneg _))
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hPXY : p ≤ p * (X * Y) :=
    le_mul_of_one_le_right hp (one_le_mul_of_one_le_of_one_le hX hY)
  have hPr : (P x : ℝ) ≤ p := by
    dsimp only [p]
    exact_mod_cast hP x
  have hceil : (R (prepare x) : ℝ) ≤ (U (prepare x) : ℝ) * X + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (U (prepare x) : ℝ) * X)).le
  have hjoin : X * Y = (2 : ℝ) ^ (((Aₜ + 16 : ℕ) : ℝ) * interpolationScale x.1) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have htarget : (Cq + 1 : ℝ) * p * (X * Y) ≤
      (((Cq + 1) * Cₚ : ℕ) : ℝ) *
        ((2 : ℝ) ^ (((Aₜ + 16 : ℕ) : ℝ) * interpolationScale x.1) *
          ((inputSize x : ℝ) + 1) ^ E) + ((Cq + 1) * Cₚ : ℕ) := by
    rw [hjoin]
    dsimp only [p]
    push_cast
    nlinarith [show (0 : ℝ) ≤ (Cq + 1) * Cₚ by positivity]
  by_cases hx : validDeclaredInput k x.1 x.2 = true
  · have hround : ((rounds (divisor ((), x.1)) x.2 + 1 : ℕ) : ℝ) ≤ Cq * Y := by
      simpa only [rounds, CNF.length_distinctVars, divisor, leafSearchDivisor, Y] using
        hq x.1 x.2.numVars (numVars_le_of_valid hx)
    have hpol : (((inputSize x + 1) ^ d + W (prepare x) : ℕ) : ℝ) ≤ p := by
      apply le_trans _ hPr
      exact_mod_cast (show (inputSize x + 1) ^ d + W (prepare x) ≤ P x by dsimp [P]; omega)
    have hinside : ((W (prepare x) + R (prepare x) : ℕ) : ℝ) ≤ p * X := by
      have hWU : ((W (prepare x) + U (prepare x) + 1 : ℕ) : ℝ) ≤ p := by
        apply le_trans _ hPr
        exact_mod_cast (show W (prepare x) + U (prepare x) + 1 ≤ P x by dsimp [P]; omega)
      have hscale := mul_le_mul_of_nonneg_right hWU (by positivity : 0 ≤ X)
      push_cast at hscale ⊢
      nlinarith [mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg (W (prepare x)))]
    have hprod := mul_le_mul hround hinside (by positivity) (by positivity)
    have hwhole := add_le_add hpol hprod
    change (((inputSize x + 1) ^ d + if validDeclaredInput k x.1 x.2 then
      W (prepare x) + (rounds (divisor ((), x.1)) x.2 + 1) *
        (W (prepare x) + R (prepare x)) else inputSize x : ℕ) : ℝ) ≤ _
    simp only [hx, ↓reduceIte, Nat.cast_add, Nat.cast_mul]
    push_cast at hwhole htarget ⊢
    apply le_trans _ htarget
    nlinarith
  · change (((inputSize x + 1) ^ d + if validDeclaredInput k x.1 x.2 then
      W (prepare x) + (rounds (divisor ((), x.1)) x.2 + 1) *
        (W (prepare x) + R (prepare x)) else inputSize x : ℕ) : ℝ) ≤ _
    simp only [hx, Bool.false_eq_true, ↓reduceIte]
    have hf : (((inputSize x + 1) ^ d + inputSize x : ℕ) : ℝ) ≤ p := by
      apply le_trans _ hPr
      exact_mod_cast (show (inputSize x + 1) ^ d + inputSize x ≤ P x by dsimp [P]; omega)
    apply hf.trans (hPXY.trans (le_trans ?_ htarget))
    calc
      p * (X * Y) ≤ ((Cq : ℝ) + 1) * (p * (X * Y)) :=
        le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg Cq))
      _ = _ := by ring

/-- Private generic join; its leaf premises are discharged by the frozen #1337 interface below. -/
private theorem exists_declared_contract_of_leaf (k : ℕ) (g : LeafInput → ℕ)
    (cg : NativeCertificate g encLeafInput encNat)
    (hcorrect : ∀ p ψ, (∀ cl ∈ ψ, cl.length ≤ k) →
      ψ.vars.toFinset ⊆ Finset.range p.2 → g (p, ψ) = ψ.modelCount)
    (hcap : ∀ x, g x ≤ 2 ^ x.2.numVars)
    (hspace : PolyBounded (fun x => (encLeafInput x).length) cg.space)
    (Cₜ dₜ Aₜ : ℕ)
    (htime : ∀ x, x.2.length ≤ leafOccBound k x.1.2 * x.1.2 + 1 →
      (cg.time x : ℝ) ≤ Cₜ * (((encLeafInput x).length : ℝ) + 1) ^ dₜ *
        (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.1.2)) :
    ∃ (count : Input → ℕ) (T S : Input → ℕ) (A c e a b : ℕ),
      ComputableInO count encInput encNat T S ∧
      (∀ x, count x = if validDeclaredInput k x.1 x.2 then
        x.2.modelCountOn (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encInput x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) := by
  let R (x : FullInput) := ⌈((Cₜ * (leafSize k x + 1) ^ dₜ : ℕ) : ℝ) *
    (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.2.1)⌉₊
  obtain ⟨Cₛ, dₛ, hspace⟩ := hspace.exists_le
  let Q (x : FullInput) := Cₛ * (leafSize k x + 1) ^ dₛ
  have hQ : PolyBounded (fun x : FullInput => (encFullInput x).length) Q :=
    (PolyBounded.const Cₛ).mul (((polyBounded_leafSize k).add (.const 1)).pow dₛ)
  obtain ⟨c, e, hsearch, hS⟩ := exists_computableInO_searchDeclaredWith
    (computableInPolyTime_divisor) (computableInPolyTime_thresholdCompare k)
    (fun p => (by decide : 1 ≤ 2).trans (two_le_thresholdBase k p))
    ((by decide : 1 ≤ 2).trans (two_le_width k)) (two_le_thresholdBase k) (le_width k)
    (treeBound k) (polyBounded_depthCoeff_full k) cg.computes
    (fun x _ i _ _ => hcap _) (R := R) (Q := Q)
    (fun x hx i _ ha => by
      obtain ⟨hclause, hlen⟩ := prefix_leaf_bounds k g x hx i ha
      let ψ := ((step (thresholdBase k (x.1, x.2.1)) (width k)
        (fun ψ => g ((x.1, x.2.1), ψ)))^[i] (init k x.2.2)).2.1.headD []
      have ht := htime ((x.1, x.2.1), ψ) hclause
      have hlenr : ((encLeafInput ((x.1, x.2.1), ψ)).length : ℝ) + 1 ≤
          (leafSize k x : ℝ) + 1 := by
        exact_mod_cast Nat.add_le_add_right hlen 1
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
        ((encLeafInput ((x.1, x.2.1), ψ)).length : ℝ) + 1) hlenr dₜ
      suffices hr : (cg.time ((x.1, x.2.1), ψ) : ℝ) ≤ (R x : ℝ) from Nat.cast_le.mp hr
      apply (ht.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg Cₜ)) (by positivity))).trans
      simpa only [R, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
        (Nat.le_ceil (((Cₜ * (leafSize k x + 1) ^ dₜ : ℕ) : ℝ) *
          (2 : ℝ) ^ ((Aₜ : ℝ) * interpolationScale x.2.1))))
    (fun x hx i _ ha => by
      have hlen := (prefix_leaf_bounds k g x hx i ha).2
      exact (hspace ((x.1, x.2.1), ((step (thresholdBase k (x.1, x.2.1)) (width k)
        (fun ψ => g ((x.1, x.2.1), ψ)))^[i] (init k x.2.2)).2.1.headD [])).trans
        (Nat.mul_le_mul_left Cₛ
        (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) dₛ))) hQ
  obtain ⟨d, hselected⟩ := exists_computableInO_selectedSearch k g hsearch
  obtain ⟨a, b, hab⟩ := (polyBounded_selectedSpace k d hS).exists_le
  obtain ⟨C, E, hT⟩ := selected_time_envelope k d c e Cₜ dₜ Aₜ
  refine ⟨_, _, _, Aₜ + 16, C, E, a, b, hselected, ?_, hT, hab⟩
  intro x
  exact searchDeclaredWith_eq_ite_modelCountOn
    ((by decide : 1 ≤ 2).trans (two_le_thresholdBase k ((), x.1)))
    ((by decide : 1 ≤ 2).trans (two_le_width k)) (two_le_thresholdBase k ((), x.1))
    (le_width k) (treeBound k ((), x.1)) (fun ψ hw _ hsub => hcorrect _ ψ hw hsub) x.2

/-- The accepted full declared-count telescope, conditional privately only on the remaining
concrete branch evaluator obligations. No leaf, prefix, clock or final-guard premise remains. -/
private theorem exists_declared_contract (k N₀_branch : ℕ) {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space)
    (hbr_time : BranchPolylogTimeBound N₀_branch cBranch) :
    ∃ (count : Input → ℕ) (T S : Input → ℕ) (A c e a b : ℕ),
      ComputableInO count encInput encNat T S ∧
      (∀ x, count x = if validDeclaredInput k x.1 x.2 then
        x.2.modelCountOn (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encInput x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) := by
  have hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n' := by
    intro n' eqs' hf
    rw [hbranch n' eqs' hf]
    exact HeavyBranchFold.rootCount_le_two_pow n' eqs'
  obtain ⟨N₀_leaf, N₀_top, Cₜ, dₜ, Aₜ, _, ht⟩ :=
    exists_branchedSparseCNF_time_bound k N₀_branch cBranch hbound hs_br hbr_time
  exact exists_declared_contract_of_leaf k
    (branchedSparseCNFLeafCounter k N₀_leaf N₀_top N₀_branch branchEval)
    (branchedSparseCNFLeafCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound)
    (fun p ψ hw hsub => branchedSparseCNFLeafCounter_eq_modelCount hbranch p.1 p.2 ψ hw hsub)
    (branchedSparseCNFLeafCounter_le_two_pow_numVars k N₀_leaf N₀_top N₀_branch branchEval)
    (polyBounded_branchedSparseCNFLeafCertificate_space k N₀_leaf N₀_top N₀_branch
      cBranch hbound hs_br) Cₜ dₜ Aₜ (fun x hx => (ht x hx).2)

/-- Reuse the existing dense-relabeling bridge; arbitrary raw variable labels are never assumed
already dense. The same remaining concrete branch premises stay explicit and private. -/
private theorem consequences_of_branch_contract (N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space)
    (hbr_time : BranchPolylogTimeBound N₀_branch cBranch) :
    (∀ k, satExponent k = 0) ∧ ¬ETH ∧ ¬SETH :=
  CountingNativeEndpointConsequencesPrep.consequences_of_declared_contract
    (fun k => exists_declared_contract k N₀_branch cBranch hbranch hs_br hbr_time)

end Cslib.Complexity.CountingNativeEndpointPrep
