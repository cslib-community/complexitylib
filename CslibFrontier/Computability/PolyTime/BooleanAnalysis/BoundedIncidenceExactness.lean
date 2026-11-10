/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
import all CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
import CslibFrontier.Foundations.Combinatorics.SharedSummaries
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact root-count correctness for the bounded-incidence branch evaluator (Proposition 5.3)

Proves the Stage-2 measurement-fiber Taylor-jet equivalence and Hermite–Cramer modular recovery
theorem `evalBoundedIncidenceBranch_eq_rootCount` for the executable bounded-incidence branch
evaluator `evalBoundedIncidenceBranch` from
`CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics`, formalizing the
semantic correctness half of Proposition 5.3 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (§§3.4–3.5, §4.6, §§5.3–5.5,
Proposition 5.3, and Appendix B.2–B.3, pp. 24–26, 33–34, 37–39, 48–50). The measurement-fiber
step instantiates the generic decoupled sum–product identity
`Cslib.SharedSummaries.sum_prod_eq_sum_measurement_fibers` on the executable group data.

Exactness holds on feasible prepared inputs (`prepareBranchEvalInput (n', eqs')` when
`checkBranchFeasible N₀_branch (n', eqs') = true`). Invalid raw `BranchEvalInput` tuples fail
`validBranchEvalParams` or the unary resource-dimension guard `validDesignShape` (which bounds
measurement and group dimensions rather than certifying arbitrary designs) and return `0`.

The proofs reuse the private scope and group-index lemmas of `BoundedIncidenceSemantics`, which
this module reads through `import all`.

## Main results

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.evalBoundedIncidenceBranch_eq_rootCount`:
  whenever `checkBranchFeasible N₀_branch (n', eqs') = true`,
  `evalBoundedIncidenceBranch (prepareBranchEvalInput (n', eqs'))` equals
  `HeavyBranchFold.rootCount n' eqs'`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§3.4–3.5, §4.6, §§5.3–5.5,
  Proposition 5.3, and Appendix B.2–B.3.
-/

@[expose] public section

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

open Finset Cslib Cslib.BitString Cslib.Complexity Cslib.GenericRAM Cslib.LinearAlgebra

/-! ### 1. Formal Cleared Parity-Factor Polynomials and Graded Degree Subring -/

section Stage2Exactness

private noncomputable def formalClearedMonomialSum {n' : ℕ} (dDen : ℤ) (k' : ℕ)
    (θ : Fin n' → Polynomial (MvPolynomial (Fin n') ℤ))
    (𝓜 : Finset (Finset (Fin n'))) : Polynomial (MvPolynomial (Fin n') ℤ) :=
  ∑ M ∈ 𝓜, Polynomial.C (MvPolynomial.C (dDen ^ (k' - #M))) * ∏ v ∈ M, θ v

private noncomputable def formalEqParityFactor {n' : ℕ} (dDen : ℤ) (k' ℓ : ℕ)
    (rows : Fin n' → Fin n' → Polynomial ℤ) (node : ℤ) (x : BitString n')
    (𝓜 : Finset (Finset (Fin n'))) : Polynomial (Polynomial (MvPolynomial (Fin n') ℤ)) :=
  parityFactorCleared ℓ (Polynomial.C (MvPolynomial.C (dDen ^ k')))
    (formalClearedMonomialSum dDen k' (fun v => Cslib.AffineTaylor.affineInput (rows v) node x) 𝓜)

private noncomputable def evalJetHom (n' J ℓ : ℕ) (y : Fin n' → ℤ) :
    Polynomial (Polynomial (MvPolynomial (Fin n') ℤ)) →+* JetTable J ℓ ℤ :=
  (JetTable.ofPolyVPolyZ J ℓ).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.eval y)))

private noncomputable def gradedDegSubring (n' : ℕ) :
    Subring (Polynomial (MvPolynomial (Fin n') ℤ)) where
  carrier := {Q | ∀ j, (Q.coeff j).totalDegree ≤ j}
  mul_mem' {P Q} hP hQ j := by
    rw [Polynomial.coeff_mul]
    have hsum_deg : ∀ s : Finset (ℕ × ℕ),
        (∀ ab ∈ s, ab.1 + ab.2 = j) →
        (∑ ab ∈ s, P.coeff ab.1 * Q.coeff ab.2).totalDegree ≤ j := by
      intro s
      induction s using Finset.cons_induction with
      | empty =>
        intro _; rw [Finset.sum_empty, MvPolynomial.totalDegree_zero]; exact Nat.zero_le j
      | cons ab s hab ih =>
        intro hs; rw [Finset.sum_cons]
        have hab_eq := hs ab (Finset.mem_cons_self ab s)
        have h1 := hP ab.1; have h2 := hQ ab.2
        have hmul : (P.coeff ab.1 * Q.coeff ab.2).totalDegree ≤ j :=
          (MvPolynomial.totalDegree_mul _ _).trans (by omega)
        exact (MvPolynomial.totalDegree_add _ _).trans
          (max_le hmul (ih fun x hx => hs x (Finset.mem_cons_of_mem hx)))
    exact hsum_deg _ fun _ hab => Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  one_mem' j := by
    by_cases hj : j = 0
    · subst hj; simp only [Polynomial.coeff_one_zero, MvPolynomial.totalDegree_one, le_rfl]
    · simp only [Polynomial.coeff_one, hj, ↓reduceIte, MvPolynomial.totalDegree_zero, Nat.zero_le]
  add_mem' {P Q} hP hQ j := by
    rw [Polynomial.coeff_add]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hP j) (hQ j))
  zero_mem' j := by simp only [Polynomial.coeff_zero, MvPolynomial.totalDegree_zero, Nat.zero_le]
  neg_mem' {P} hP j := by rw [Polynomial.coeff_neg, MvPolynomial.totalDegree_neg]; exact hP j

private theorem const_mem_gradedDegSubring (n' : ℕ) (c : ℤ) :
    Polynomial.C (MvPolynomial.C c) ∈ gradedDegSubring n' := fun j => by
  rw [Polynomial.coeff_C]
  by_cases hj : j = 0
  · subst hj; simp only [↓reduceIte, MvPolynomial.totalDegree_C, le_rfl]
  · simp only [hj, ↓reduceIte, MvPolynomial.totalDegree_zero, Nat.zero_le]

private theorem formalClearedMonomialSum_mem_gradedDegSubring {n' : ℕ} (dDen : ℤ) (k' : ℕ)
    (rows : Fin n' → Fin n' → Polynomial ℤ) (node : ℤ) (x : BitString n')
    (𝓜 : Finset (Finset (Fin n'))) :
    formalClearedMonomialSum dDen k' (fun v => Cslib.AffineTaylor.affineInput (rows v) node x) 𝓜 ∈
      gradedDegSubring n' :=
  Subring.sum_mem _ fun _ _ =>
    Subring.mul_mem _ (const_mem_gradedDegSubring n' _)
      (Subring.prod_mem _ fun v _ j =>
        Cslib.AffineTaylor.totalDegree_coeff_affineInput_le (rows v) node x j)

private theorem totalDegree_coeff_prod_formalEqParityFactor_le {κ : Type*} {n' : ℕ}
    (I_eq : Finset κ) (dDen : ℤ) (k' ℓ : ℕ) (rows : κ → Fin n' → Fin n' → Polynomial ℤ)
    (node : ℤ) (x : BitString n') (P_eq : κ → Finset (Finset (Fin n'))) (s j : ℕ) :
    ((((∏ f ∈ I_eq, formalEqParityFactor dDen k' ℓ (rows f) node x (P_eq f)).coeff s).coeff
        j)).totalDegree ≤ j := by
  let S := gradedDegSubring n'
  let ΔS : S := ⟨Polynomial.C (MvPolynomial.C (dDen ^ k')), const_mem_gradedDegSubring n' _⟩
  let AS : κ → S := fun f =>
    ⟨formalClearedMonomialSum dDen k'
        (fun v => Cslib.AffineTaylor.affineInput (rows f v) node x) (P_eq f),
      formalClearedMonomialSum_mem_gradedDegSubring dDen k' (rows f) node x (P_eq f)⟩
  have hprod : (∏ f ∈ I_eq, formalEqParityFactor dDen k' ℓ (rows f) node x (P_eq f)) =
      (∏ f ∈ I_eq, parityFactorCleared ℓ ΔS (AS f)).map S.subtype := by
    rw [Polynomial.map_prod]
    exact Finset.prod_congr rfl fun f _ => (map_parityFactorCleared S.subtype ℓ ΔS (AS f)).symm
  rw [hprod, Polynomial.coeff_map]
  exact (((∏ f ∈ I_eq, parityFactorCleared ℓ ΔS (AS f)).coeff s)).2 j

/-! ### 2. Per-Equation Jet Evaluation and Measurement-Fiber Baseline Invariance -/

private theorem length_lookupReplacementRow_le {n' D_cap Q r A₀ R : ℕ}
    (augScopes sv ss : List (List ℕ)) (f v : ℕ) :
    ((buildReplacementDesignData n' D_cap Q r A₀ R augScopes sv ss).lookupReplacementRow
      f v).length ≤ n' := by
  let data := buildReplacementDesignData n' D_cap Q r A₀ R augScopes sv ss
  change (data.replacementRows.getD (data.incidences.idxOf (f, v)) []).length ≤ n'
  by_cases hlt : data.incidences.idxOf (f, v) < data.replacementRows.length
  · rw [List.getD_eq_getElem _ [] hlt]
    let row := data.replacementRows[data.incidences.idxOf (f, v)]
    have hmem : row ∈ data.replacementRows := List.getElem_mem hlt
    dsimp only [data, buildReplacementDesignData] at hmem
    obtain ⟨e, _, he_eq⟩ := List.mem_map.mp hmem
    change row.length ≤ n'
    rw [← he_eq, CopyPlacement.pullbackReplacementRow]
    exact (isTableShape_tabulateTable n' R _).1.le
  · rw [List.getD_eq_default _ [] (Nat.not_lt.mp hlt)]
    exact Nat.zero_le n'

private theorem toJetTable_evalEquationParityFactorJet_eq {n' J ℓ k' : ℕ} (dDen node : ℤ)
    {rowsCoeffs : List (List (List ℤ))} (hrows_len : ∀ r_tbl ∈ rowsCoeffs, r_tbl.length ≤ n')
    (indU xList : List Bool) {eq : List (List ℕ)} (heq : IsCanonicalEquation eq)
    (hdeg : ∀ mon ∈ eq, mon.length ≤ k') (hvars : ∀ mon ∈ eq, ∀ v ∈ mon, v < n') :
    CommonCountingAccum.toJetTable J ℓ
        (evalEquationParityFactorJet J ℓ k' dDen
          (evalAffineInputZJetTable J node rowsCoeffs indU xList) eq) =
      evalJetHom n' J ℓ (fun i => bitVal ℤ (indU.getD i.1 false))
        (formalEqParityFactor dDen k' ℓ
          (fun v i => Polynomial.ofCoeffList ((rowsCoeffs.getD v.1 []).getD i.1 []))
          node (fun i => xList.getD i.1 false) (HeavyBranchFold.toFinsetEquation n' eq)) := by
  let y : Fin n' → ℤ := fun i => bitVal ℤ (indU.getD i.1 false)
  let x : Fin n' → Bool := fun i => xList.getD i.1 false
  let rowsNat : ℕ → Fin n' → Polynomial ℤ := fun v i =>
    Polynomial.ofCoeffList ((rowsCoeffs.getD v []).getD i.1 [])
  let θ : ℕ → Polynomial ℤ := fun v =>
    (Cslib.AffineTaylor.affineInput (rowsNat v) node x).map (MvPolynomial.eval y)
  apply JetTable.ext; intro j u
  rw [CommonCountingAccum.toJetTable_apply,
    evalEquationParityFactorJet_entry_eq_parityFactorCleared j.isLt ℓ u.1 dDen heq hdeg
      (θ := θ) (fun _ _ v _ i hi =>
        rowEntry_evalAffineInputZJetTable_eq_coeff_affineInput hi node hrows_len indU xList v)]
  have himg_m : ∀ m ∈ eq,
      Finset.image Fin.val ({i : Fin n' | i.1 ∈ m} : Finset (Fin n')) = m.toFinset := by
    intro m hm; ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    exact ⟨by rintro ⟨i, hi, rfl⟩; exact hi, fun hw => ⟨⟨w, hvars m hm w hw⟩, hw, rfl⟩⟩
  have heq_img : (eq.map List.toFinset).toFinset =
      (HeavyBranchFold.toFinsetEquation n' eq).image (Finset.image Fin.val) := by
    ext S
    simp only [HeavyBranchFold.toFinsetEquation, Finset.mem_image, List.mem_toFinset, List.mem_map]
    exact ⟨by rintro ⟨m, hm, rfl⟩; exact ⟨_, ⟨m, hm, rfl⟩, himg_m m hm⟩,
      by rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩; exact ⟨m, hm, (himg_m m hm).symm⟩⟩
  have hsum_eq : clearedMonomialSumPoly dDen k' θ (eq.map List.toFinset).toFinset =
      (formalClearedMonomialSum dDen k'
        (fun v => Cslib.AffineTaylor.affineInput (rowsNat v.1) node x)
        (HeavyBranchFold.toFinsetEquation n' eq)).map (MvPolynomial.eval y) := by
    rw [clearedMonomialSumPoly, heq_img,
      Finset.sum_image (fun _ _ _ _ h => Finset.image_injective Fin.val_injective h),
      formalClearedMonomialSum, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [clearedMonomialPoly, Finset.card_image_of_injective M Fin.val_injective,
      Finset.prod_image (fun _ _ _ _ h => Fin.ext h), Polynomial.map_mul, Polynomial.map_C,
      MvPolynomial.eval_C, Polynomial.map_prod]
  change _ = (evalJetHom n' J ℓ y _) j u
  simp only [evalJetHom, RingHom.comp_apply, JetTable.ofPolyVPolyZ_apply,
    Polynomial.coe_mapRingHom, formalEqParityFactor,
    map_parityFactorCleared (Polynomial.mapRingHom (MvPolynomial.eval y)),
    Polynomial.map_C, MvPolynomial.eval_C]
  rw [hsum_eq]

private theorem evalBoolRow_restrictGroup_eq_sum (Vg : List ℕ) (row : List ℤ)
    (ug : BitString Vg.length) :
    BooleanMeasurements.evalBoolRow (Vg.map fun v => row.getD v 0) (List.ofFn ug) =
      ∑ j : Fin Vg.length, row.getD Vg[j] 0 * bitVal ℤ (ug j) := by
  unfold BooleanMeasurements.evalBoolRow
  rw [List.length_map, List.sum_map_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.getD_eq_getElem (List.ofFn ug) false (by simp only [List.length_ofFn]; exact j.2),
    List.getElem_ofFn, List.getD_eq_getElem _ 0 (by simp only [List.length_map]; exact j.2),
    List.getElem_map, Fin.getElem_fin]
  cases ug j <;> simp only [bitVal, mul_zero, mul_one, ↓reduceIte, Bool.false_eq_true]

private theorem localBitsEquiv_apply_of_eq {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g)
    (u : ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) {v : Fin n'} {g : Fin r}
    (hv : varAssign v = g) :
    localBitsEquiv hVG u v = u g ((groupIdxEquiv hVG g).symm ⟨v, hv⟩) :=
  Cslib.ReplacementCounting.piGroupEquiv_apply_of_eq varAssign _ hv

private theorem sum_measurementRow_localBitsEquiv_eq {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g)
    (row : List ℤ) (u : ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) :
    (∑ i : Fin n', row.getD i.1 0 * bitVal ℤ (localBitsEquiv hVG u i)) =
      ∑ g : Fin r, BooleanMeasurements.evalBoolRow
        ((vGroups_t.getD g.1 []).map fun v => row.getD v 0) (List.ofFn (u g)) := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (varAssign i))]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [evalBoolRow_restrictGroup_eq_sum]
  have hfib : (univ.filter fun i : Fin n' => varAssign i = g) =
      univ.image (fun j : Fin (vGroups_t.getD g.1 []).length => (groupIdxEquiv hVG g j).1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨fun hi => ⟨(groupIdxEquiv hVG g).symm ⟨i, hi⟩,
      congrArg Subtype.val ((groupIdxEquiv hVG g).apply_symm_apply ⟨i, hi⟩)⟩, fun ⟨j, hj⟩ => ?_⟩
    rw [← hj]; exact (groupIdxEquiv hVG g j).2
  rw [hfib, Finset.sum_image (fun _ _ _ _ h => (groupIdxEquiv hVG g).injective (Subtype.ext h))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlbe : localBitsEquiv hVG u (groupIdxEquiv hVG g j).1 = u g j := by
    rw [localBitsEquiv_apply_of_eq hVG u (groupIdxEquiv hVG g j).2]
    exact congrArg (u g) ((groupIdxEquiv hVG g).symm_apply_apply j)
  rw [val_groupIdxEquiv hVG g j, hlbe]

/-- A cleared parity factor reads its rows and input bits only on the variables of its equation:
if the affine inputs agree on `equationScope 𝓜`, so do the factors. -/
private theorem formalEqParityFactor_congr {n' : ℕ} (dDen : ℤ) (k' ℓ : ℕ)
    {rows rows' : Fin n' → Fin n' → Polynomial ℤ} (node : ℤ) {x x' : BitString n'}
    {𝓜 : Finset (Finset (Fin n'))}
    (h : ∀ v ∈ equationScope 𝓜, Cslib.AffineTaylor.affineInput (rows v) node x =
      Cslib.AffineTaylor.affineInput (rows' v) node x') :
    formalEqParityFactor dDen k' ℓ rows node x 𝓜 =
      formalEqParityFactor dDen k' ℓ rows' node x' 𝓜 := by
  apply congrArg (parityFactorCleared ℓ _)
  refine Finset.sum_congr rfl fun M hM => ?_
  apply congrArg (_ * ·)
  refine Finset.prod_congr rfl fun v hvM => ?_
  exact h v (Finset.mem_biUnion.mpr ⟨M, hM, hvM⟩)

/-- Local bit assignments with equal group measurements and equal bits on the factor's group
give equal cleared parity factors for any equation scoped inside that factor. -/
private theorem formalEqParityFactor_congr_fiber {n' D_cap Q r A₀ R k' ℓ : ℕ} {τ : ℚ}
    {augScopes sv ss : List (List ℕ)} {data : ReplacementDesignData}
    (hdata : data = buildReplacementDesignData n' D_cap Q r A₀ R augScopes sv ss)
    {D : ReplacementDesign (listScopeFamily n' augScopes) Q r A₀ R τ}
    (href : data.Refines augScopes D) (t : Fin Q)
    (hVG : ∀ g : Fin r, ((data.varGroups.getD t.1 []).getD g.1 []).Nodup ∧
      (∀ w ∈ (data.varGroups.getD t.1 []).getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ (data.varGroups.getD t.1 []).getD g.1 [] ↔ D.varAssign v t = g)
    (f_aug : Fin augScopes.length) {g : Fin r} (hfg : D.factorAssign f_aug t = g)
    {𝓜 : Finset (Finset (Fin n'))}
    (hscope : equationScope 𝓜 ⊆ listScopeFamily n' augScopes f_aug) (dDen : ℤ)
    (x x' : ∀ h : Fin r, BitString ((data.varGroups.getD t.1 []).getD h.1 []).length)
    (hmeas_eq : ∀ h : Fin r,
      BooleanMeasurements.evalBoolMatrix ((data.groupMeasurementMatrices.getD t.1 []).getD h.1 [])
        (List.ofFn (x h)) =
      BooleanMeasurements.evalBoolMatrix ((data.groupMeasurementMatrices.getD t.1 []).getD h.1 [])
        (List.ofFn (x' h))) (hg_eq : x g = x' g) :
    let scope := listScopeFamily n' augScopes
    let rows : Fin n' → Fin n' → Polynomial ℤ := fun v i =>
      if hv : v ∈ scope f_aug then
        varReplacementRowScaledInt Q r A₀ R D.place (BalancedSchedules.scopeVarOf scope)
          ⟨f_aug, ⟨v, hv⟩⟩ i
      else 0
    formalEqParityFactor dDen k' ℓ rows ((t.1 : ℤ) + 1) (localBitsEquiv hVG x) 𝓜 =
      formalEqParityFactor dDen k' ℓ rows ((t.1 : ℤ) + 1) (localBitsEquiv hVG x') 𝓜 := by
  intro scope rows
  subst hfg
  let x₁ := localBitsEquiv hVG x
  let x₂ := localBitsEquiv hVG x'
  have hmulVec : (varMeasurementMatrix Q r A₀ R ℚ D.place
        (BalancedSchedules.scopeVarOf scope)).mulVec (fun i => bitVal ℚ (x₁ i)) =
      (varMeasurementMatrix Q r A₀ R ℚ D.place
        (BalancedSchedules.scopeVarOf scope)).mulVec (fun i => bitVal ℚ (x₂ i)) := by
    rw [← sub_eq_zero, ← Matrix.mulVec_sub]
    change (varMeasurementMatrix Q r A₀ R ℚ D.place (BalancedSchedules.scopeVarOf scope)).mulVec
      (fun i => bitVal ℚ (x₁ i) - bitVal ℚ (x₂ i)) = 0
    rw [href.2.2.2.2.2.1]
    intro row hrow
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hrow
    have hint_eq : (∑ i : Fin n', data.measurementMatrix[idx].getD i.1 0 * bitVal ℤ (x₁ i)) =
        (∑ i : Fin n', data.measurementMatrix[idx].getD i.1 0 * bitVal ℤ (x₂ i)) := by
      rw [sum_measurementRow_localBitsEquiv_eq hVG, sum_measurementRow_localBitsEquiv_eq hVG]
      refine Finset.sum_congr rfl fun h _ => ?_
      have hCth : (data.groupMeasurementMatrices.getD t.1 []).getD h.1 [] =
          CopyPlacement.restrictGroupColumns ((data.varGroups.getD t.1 []).getD h.1 [])
            data.measurementMatrix := by
        subst hdata; dsimp only [buildReplacementDesignData]
        rw [List.map_map, List.getD_map_range _ [] t.2, Function.comp_apply, List.map_map,
          List.getD_map_range _ [] h.2, Function.comp_apply,
          List.getD_map_range _ [] t.2, List.getD_map_range _ [] h.2]
      have hrow (y : ∀ h : Fin r, BitString ((data.varGroups.getD t.1 []).getD h.1 []).length) :
          (BooleanMeasurements.evalBoolMatrix ((data.groupMeasurementMatrices.getD t.1 []).getD h.1
            []) (List.ofFn (y h))).getD idx 0 =
          BooleanMeasurements.evalBoolRow (((data.varGroups.getD t.1 []).getD h.1 []).map
            fun v => data.measurementMatrix[idx].getD v 0) (List.ofFn (y h)) := by
        rw [hCth]
        dsimp only [BooleanMeasurements.evalBoolMatrix, CopyPlacement.restrictGroupColumns]
        rw [List.getD_eq_getElem _ 0 (by simp only [List.length_map]; exact hidx),
          List.getElem_map, List.getElem_map]
      simpa only [hrow] using congrArg (fun L : List ℤ => L.getD idx 0) (hmeas_eq h)
    have hbit : ∀ b : Bool, ((bitVal ℤ b : ℤ) : ℚ) = bitVal ℚ b := fun b => by cases b <;> rfl
    have hq_eq : (∑ i : Fin n', (data.measurementMatrix[idx].getD i.1 0 : ℚ) * bitVal ℚ (x₁ i)) =
        (∑ i : Fin n', (data.measurementMatrix[idx].getD i.1 0 : ℚ) * bitVal ℚ (x₂ i)) := by
      simpa only [Int.cast_sum, Int.cast_mul, hbit] using congrArg (Int.cast : ℤ → ℚ) hint_eq
    simp only [mul_sub, Finset.sum_sub_distrib, hq_eq, sub_self]
  have hgrp : ∀ w ∈ varGroup D.varAssign t (D.factorAssign f_aug t), x₁ w = x₂ w := fun w hw => by
    have key : ∀ h, h = D.factorAssign f_aug t → x h = x' h := by rintro h rfl; exact hg_eq
    dsimp only [x₁, x₂]
    rw [localBitsEquiv_apply hVG, localBitsEquiv_apply hVG, key _ (mem_varGroup.mp hw)]
  refine formalEqParityFactor_congr dDen k' ℓ _ fun v hv => ?_
  have hv_sc : v ∈ scope f_aug := hscope hv
  let e : BalancedSchedules.ScopeIncidence scope := ⟨f_aug, ⟨v, hv_sc⟩⟩
  have hrows_v : rows v =
      varReplacementRowScaledInt Q r A₀ R D.place (BalancedSchedules.scopeVarOf scope) e := by
    funext i; simp only [rows, hv_sc, ↓reduceDIte]; rfl
  rw [hrows_v]
  apply Cslib.AffineTaylor.affineInput_congr_baseline
  have heval_q := eval_evalVarReplacementRowPoly_nodePoint_eq_of_eq_on_varGroup D e t x₁ x₂
    hgrp hmulVec
  have hscaled_q :
      ((evalVarReplacementRowScaledIntPoly D e x₁).map (Int.castRingHom ℚ)).eval (nodePoint t) =
      ((evalVarReplacementRowScaledIntPoly D e x₂).map (Int.castRingHom ℚ)).eval (nodePoint t) := by
    rw [map_evalVarReplacementRowScaledIntPoly, map_evalVarReplacementRowScaledIntPoly,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, heval_q]
  have hnode_eq : (nodePoint t : ℚ) = Int.castRingHom ℚ ((t.1 : ℤ) + 1) := by
    simp only [nodePoint, Int.coe_castRingHom, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [hnode_eq, Polynomial.eval_map_apply, Polynomial.eval_map_apply] at hscaled_q
  simp only [Int.coe_castRingHom] at hscaled_q
  have hint_eval := Int.cast_injective hscaled_q
  have heval_sum (x : Fin n' → Bool) :
      (evalVarReplacementRowScaledIntPoly D e x).eval ((t.1 : ℤ) + 1) =
        ∑ i : Fin n', (varReplacementRowScaledInt Q r A₀ R D.place
          (BalancedSchedules.scopeVarOf scope) e i).eval ((t.1 : ℤ) + 1) * bitVal ℤ (x i) := by
    dsimp only [evalVarReplacementRowScaledIntPoly]
    rw [← Polynomial.coe_evalRingHom, map_sum]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, mul_comm, scope]
  rwa [heval_sum x₁, heval_sum x₂] at hint_eval

/-- Index of the scope of the `f`-th equation in the neutral-scope-augmented scope family; the
equation scopes come first. -/
private def eqScopeIndex (n' : ℕ) (eqs' : List (List (List ℕ))) (f : Fin eqs'.length) :
    Fin (withNeutralScopesList (eqs'.map equationVars) n').length :=
  withNeutralScopesIndexEquiv (eqs'.map equationVars) n'
    (Sum.inl ⟨f.1, by simp only [List.length_map]; exact f.2⟩)

/-- The equation scope index has the equation's own index as its value. -/
private theorem val_eqScopeIndex (n' : ℕ) (eqs' : List (List (List ℕ))) (f : Fin eqs'.length) :
    (eqScopeIndex n' eqs' f).1 = f.1 :=
  val_withNeutralScopesIndexEquiv_inl _ _ _

/-- The augmented scope of the `f`-th equation is the variable scope of that equation. -/
private theorem listScopeFamily_eqScopeIndex (n' : ℕ) (eqs' : List (List (List ℕ)))
    (f : Fin eqs'.length) :
    listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n') (eqScopeIndex n' eqs' f) =
      equationScope (HeavyBranchFold.toFinsetEquation n' (eqs'[f.1]'f.isLt)) := by
  rw [eqScopeIndex, listScopeFamily_withNeutralScopesList]
  exact listScopeFamily_map_equationVars n' eqs' f

/-- Scaled integer replacement rows of the design `D` on the scope of the `f`-th equation,
extended by zero outside that scope. -/
private noncomputable def eqDesignRows {n' Q r A₀ R : ℕ} {τ : ℚ} {eqs' : List (List (List ℕ))}
    (D : ReplacementDesign (listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n'))
      Q r A₀ R τ) (f : Fin eqs'.length) (v i : Fin n') : Polynomial ℤ :=
  let scope := listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n')
  if hv : v ∈ scope (eqScopeIndex n' eqs' f) then
    varReplacementRowScaledInt Q r A₀ R D.place (BalancedSchedules.scopeVarOf scope)
      ⟨eqScopeIndex n' eqs' f, ⟨v, hv⟩⟩ i
  else 0

/-! ### 3. Measurement-Tuple Coverage and Two-Pass Fiber Jet Fold Equivalence -/

private theorem sliceBlocks_iff_eq_flatten {r m : ℕ} (L : Fin r → List ℤ)
    (hL : ∀ g : Fin r, (L g).length = m) {word : List ℤ} (hw : word.length = r * m) :
    (∀ g : Fin r, (word.drop (g.1 * m)).take m = L g) ↔ word = (List.ofFn L).flatten := by
  induction r generalizing word with
  | zero =>
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at hw; subst hw
    exact ⟨fun _ => rfl, fun _ g => Fin.elim0 g⟩
  | succ r ih =>
    have hm_le : m ≤ word.length := by rw [hw, Nat.succ_mul]; omega
    have htake_len : (word.take m).length = m := List.length_take_of_le hm_le
    have hdrop_len : (word.drop m).length = r * m := by
      rw [List.length_drop, hw, Nat.succ_mul]; omega
    rw [List.ofFn_succ, List.flatten_cons]
    refine ⟨fun h => ?_, fun h g => ?_⟩
    · have h0 : word.take m = L 0 := by
        simpa only [Fin.val_zero, Nat.zero_mul, List.drop_zero] using h 0
      have hrest : word.drop m = (List.ofFn fun g : Fin r => L g.succ).flatten :=
        (ih (fun g => L g.succ) (fun g => hL g.succ) hdrop_len).mp fun g => by
          simpa only [Fin.val_succ, Nat.succ_mul, add_comm _ m, List.drop_drop] using h g.succ
      rw [← List.take_append_drop m word, h0, hrest]
    · have happ : word.take m ++ word.drop m =
          L 0 ++ (List.ofFn fun i : Fin r => L i.succ).flatten := by rwa [List.take_append_drop]
      obtain ⟨h0, hrest⟩ := List.append_inj happ (htake_len.trans (hL 0).symm)
      refine Fin.cases (by simpa only [Fin.val_zero, Nat.zero_mul, List.drop_zero] using h0)
        (fun g' => ?_) g
      rw [Fin.val_succ, Nat.succ_mul, add_comm _ m, ← List.drop_drop]
      exact (ih (fun i => L i.succ) (fun i => hL i.succ) hdrop_len).mpr hrest g'

private theorem natAbs_evalBoolRow_le_sum (row : List ℤ) (bs : List Bool) :
    (BooleanMeasurements.evalBoolRow row bs).natAbs ≤ (row.map Int.natAbs).sum := by
  unfold BooleanMeasurements.evalBoolRow
  conv_rhs => rw [← List.map_getD_range row 0, List.map_map]
  rw [List.sum_map_range, List.sum_map_range]
  refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- On the scope of the `f`-th equation, `eqDesignRows` is the scaled integer replacement row of
the corresponding incidence. -/
private theorem eqDesignRows_of_mem {n' Q r A₀ R : ℕ} {τ : ℚ} {eqs' : List (List (List ℕ))}
    (D : ReplacementDesign (listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n'))
      Q r A₀ R τ) (f : Fin eqs'.length) {v : Fin n'}
    (hv : v ∈ listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n')
      (eqScopeIndex n' eqs' f)) :
    eqDesignRows D f v = varReplacementRowScaledInt Q r A₀ R D.place
      (BalancedSchedules.scopeVarOf _) ⟨eqScopeIndex n' eqs' f, ⟨v, hv⟩⟩ :=
  funext fun _ => dite_eq_left hv

/-- A left fold whose step keeps a fixed context `c`, and acts on the accumulator through `φ` as
`step'` does, is after `φ` the fold of `step'`. -/
private theorem foldl_fixedContext {γ α β ι : Type*} (step : γ × α → ι → γ × α) (φ : α → β)
    (step' : β → ι → β) (c : γ)
    (hstep : ∀ acc w, (step (c, acc) w).1 = c ∧ φ (step (c, acc) w).2 = step' (φ acc) w)
    (ws : List ι) (acc : α) :
    φ (ws.foldl step (c, acc)).2 = ws.foldl step' (φ acc) := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    have hst : step (c, acc) w = (c, (step (c, acc) w).2) := Prod.ext (hstep acc w).1 rfl
    rw [List.foldl_cons, List.foldl_cons, hst, ih, (hstep acc w).2]

/-- Reindexing decoded signed measurement words by the measurement box. When every local
measurement is a length-`m` word with entries in `[-D, D]`, each realizable measurement tuple is
the block decomposition of exactly one radix index, so a sum over the radix indices of a summand
that vanishes off realizable tuples is the sum over the box. -/
private theorem sum_radix_eq_sum_piFinset_image {r m D : ℕ} {X : Fin r → Type*}
    [∀ g, Fintype (X g)] {A : Type*} [AddCommMonoid A] (meas : ∀ g, X g → List ℤ)
    (hlen : ∀ g x, (meas g x).length = m)
    (hbound : ∀ g x, ∀ z ∈ meas g x, -(D : ℤ) ≤ z ∧ z ≤ D)
    (F : (Fin r → List ℤ) → A) (hF : ∀ y, F y ≠ 0 → ∀ g, ∃ x, meas g x = y g) :
    ∑ idx : Fin ((2 * D + 1) ^ (r * m)),
        F (fun g => ((Cslib.Radix.measurementValues (r * m) D idx.1).drop (g.1 * m)).take m) =
      ∑ y ∈ Fintype.piFinset fun g => univ.image (meas g), F y := by
  let mv := Cslib.Radix.measurementValues (r * m) D
  let split : List ℤ → Fin r → List ℤ := fun word g => (word.drop (g.1 * m)).take m
  have hcov (u : ∀ g, X g) :
      ∃! idx : Fin ((2 * D + 1) ^ (r * m)), split (mv idx.1) = fun g => meas g (u g) := by
    have hW_len : (List.ofFn fun g => meas g (u g)).flatten.length = r * m := by
      simp only [List.length_flatten, List.map_ofFn, Function.comp_def, hlen, List.sum_ofFn,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hW_bnd : ∀ z ∈ (List.ofFn fun g => meas g (u g)).flatten, -(D : ℤ) ≤ z ∧ z ≤ D := by
      intro z hz
      obtain ⟨sub, hsub, hz_sub⟩ := List.mem_flatten.mp hz
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hsub
      exact hbound g (u g) z hz_sub
    obtain ⟨idx, hidx, huniq⟩ := Cslib.Radix.measurementValues_coverage (r * m) D _ hW_len hW_bnd
    have hsplit (j : Fin ((2 * D + 1) ^ (r * m))) : split (mv j.1) = (fun g => meas g (u g)) ↔
        mv j.1 = (List.ofFn fun g => meas g (u g)).flatten :=
      funext_iff.trans (sliceBlocks_iff_eq_flatten _ (fun g => hlen g (u g))
        (Cslib.Radix.length_measurementValues (r * m) D j.1))
    exact ⟨idx, (hsplit idx).mpr hidx, fun j hj => huniq j ((hsplit j).mp hj)⟩
  refine Finset.sum_bij_ne_zero (fun idx _ _ => split (mv idx.1)) ?_ ?_ ?_ fun _ _ _ => rfl
  · intro idx _ hne
    refine Fintype.mem_piFinset.mpr fun g => ?_
    obtain ⟨x, hx⟩ := hF _ hne g
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
  · intro a _ ha b _ _ hab
    choose u hu using hF _ ha
    have hua : split (mv a.1) = fun g => meas g (u g) := funext fun g => (hu g).symm
    exact (hcov u).unique hua (hab.symm.trans hua)
  · intro y _ hne
    choose u hu using hF y hne
    obtain ⟨idx, hidx, -⟩ := hcov u
    have hy : split (mv idx.1) = y := hidx.trans (funext hu)
    refine ⟨idx, Finset.mem_univ _, ?_, hy⟩
    change F (split (mv idx.1)) ≠ 0
    rwa [hy]

/-- Under `localBitsEquiv`, the product of the `indE`-restricted local cubes is the restricted
global cube `{x | ∀ i ∈ supportOfList n' indE, x i = true}`. -/
private theorem sum_piFinset_checkRestrictedGroup_eq {n' r : ℕ} {vGroups_t : List (List ℕ)}
    {varAssign : Fin n' → Fin r}
    (hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ varAssign v = g)
    (indE : List Bool) {A : Type*} [AddCommMonoid A] (F : (Fin n' → Bool) → A) :
    ∑ u ∈ Fintype.piFinset (fun g : Fin r =>
        univ.filter fun ug : BitString (vGroups_t.getD g.1 []).length =>
          checkRestrictedGroup n' indE (vGroups_t.getD g.1 []) (List.ofFn ug) = true),
        F (localBitsEquiv hVG u) =
      ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ supportOfList n' indE, x i = true),
        F x := by
  refine Finset.sum_equiv (localBitsEquiv hVG) (fun u => ?_) fun _ _ => rfl
  simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h i hi => ?_, fun h g =>
    (checkRestrictedGroup_ofFn_iff indE (hVG g).2.1 (u g)).mpr fun j hj => ?_⟩
  · rw [localBitsEquiv_apply hVG]
    have hv : ((groupIdxEquiv hVG _) ((groupIdxEquiv hVG (varAssign i)).symm ⟨i, rfl⟩)).1 =
        i := congrArg Subtype.val ((groupIdxEquiv hVG _).apply_symm_apply ⟨i, rfl⟩)
    exact (checkRestrictedGroup_ofFn_iff indE (hVG _).2.1 _).mp (h _) _ (by rwa [← hv] at hi)
  · have h' := h (groupIdxEquiv hVG g j).1 hj
    rwa [localBitsEquiv_apply_of_eq hVG u (groupIdxEquiv hVG g j).2,
      (groupIdxEquiv hVG g).symm_apply_apply] at h'

/-- At node `t`, the executable product of cleared parity-factor jets over the equations that
`groupEquationsAt` assigns to group `g` is the jet of the formal product over the equations whose
design factor group is `g`, evaluated at the Boolean point `indU`. -/
private theorem toJetTable_prodJet_groupEquationsAt {n' Q r A₀ R J ℓ k' : ℕ} {τ : ℚ}
    {eqs' : List (List (List ℕ))} {sv ss : List (List ℕ)}
    (hcan : ∀ eq ∈ eqs', IsCanonicalEquation eq)
    (hvars : ∀ eq ∈ eqs', ∀ m ∈ eq, ∀ v ∈ m, v < n')
    (hk_deg : ∀ eq ∈ eqs', ∀ m ∈ eq, m.length ≤ k')
    {data : ReplacementDesignData}
    (hdata : data = buildReplacementDesignData n' (r ^ (2 * Q)) Q r A₀ R
      (withNeutralScopesList (eqs'.map equationVars) n') sv ss)
    {D : ReplacementDesign (listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n'))
      Q r A₀ R τ}
    (href : data.Refines (withNeutralScopesList (eqs'.map equationVars) n') D)
    (t : Fin Q) (g : Fin r) (dDen node : ℤ) (indU xList : List Bool) :
    CommonCountingAccum.toJetTable J ℓ
        (CommonCountingAccum.prodJet J ℓ
          ((groupEquationsAt eqs' data.factorGroups (buildEqRowTables n' eqs' data) t.1 g).map
            fun eqPair => evalEquationParityFactorJet J ℓ k' dDen
              (evalAffineInputZJetTable J node eqPair.2 indU xList) eqPair.1)) =
      evalJetHom n' J ℓ (fun i => bitVal ℤ (decide (i ∈ supportOfList n' indU)))
        (∏ f ∈ univ.filter (fun f : Fin eqs'.length =>
            D.factorAssign (eqScopeIndex n' eqs' f) t = g),
          formalEqParityFactor dDen k' ℓ (eqDesignRows D f) node (fun i => xList.getD i.1 false)
            (HeavyBranchFold.toFinsetEquation n' (eqs'[f.1]'f.isLt))) := by
  rw [CommonCountingAccum.toJetTable_prodJet]
  unfold groupEquationsAt
  rw [← List.map_coe_finRange_eq_range, List.filter_map, List.map_map, List.map_map,
    List.map_map]
  let p_pred : Fin eqs'.length → Bool := fun f =>
    decide ((data.factorGroups.getD f.1 []).getD t.1 0 = g.1)
  let F_jet : Fin eqs'.length → JetTable J ℓ ℤ := fun f =>
    evalJetHom n' J ℓ (fun i => bitVal ℤ (decide (i ∈ supportOfList n' indU)))
      (formalEqParityFactor dDen k' ℓ (eqDesignRows D f) node (fun i => xList.getD i.1 false)
        (HeavyBranchFold.toFinsetEquation n' (eqs'[f.1]'f.isLt)))
  have hy_U : (fun i : Fin n' => bitVal ℤ (indU.getD i.1 false)) =
      fun i => bitVal ℤ (decide (i ∈ supportOfList n' indU)) :=
    funext fun i => congrArg (bitVal ℤ) (Bool.eq_iff_iff.mpr
      (by simp only [decide_eq_true_eq, mem_supportOfList]))
  -- Each executable equation jet is the jet of its formal parity factor with the design rows.
  have hmap_eq : List.map
      (((CommonCountingAccum.toJetTable J ℓ ∘ fun eqPair : List (List ℕ) × List (List (List ℤ)) =>
          evalEquationParityFactorJet J ℓ k' dDen
            (evalAffineInputZJetTable J node eqPair.2 indU xList) eqPair.1) ∘
        fun f : ℕ => (eqs'.getD f [], (buildEqRowTables n' eqs' data).getD f [])) ∘ Fin.val)
      ((List.finRange eqs'.length).filter p_pred) =
      ((List.finRange eqs'.length).filter p_pred).map F_jet := by
    refine List.map_congr_left fun f _ => ?_
    simp only [Function.comp_apply, List.getD_eq_getElem eqs' [] f.2]
    have hert : (buildEqRowTables n' eqs' data).getD f.1 [] =
        (List.range n').map fun v => data.lookupReplacementRow f.1 v :=
      List.getD_map_range _ [] f.2
    have hrows_len : ∀ r_tbl ∈ (buildEqRowTables n' eqs' data).getD f.1 [], r_tbl.length ≤ n' := by
      rw [hert]; intro r_tbl hr_tbl
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr_tbl
      rw [hdata]; exact length_lookupReplacementRow_le _ _ _ _ _
    have hf_mem := List.getElem_mem f.2
    rw [toJetTable_evalEquationParityFactorJet_eq dDen node hrows_len indU xList
      (hcan _ hf_mem) (hk_deg _ hf_mem) (hvars _ hf_mem), hy_U]
    refine congrArg (evalJetHom n' J ℓ _) (formalEqParityFactor_congr dDen k' ℓ node fun v hv => ?_)
    have hv_sc : v ∈ listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n')
        (eqScopeIndex n' eqs' f) := by
      rwa [listScopeFamily_eqScopeIndex]
    refine congrArg (fun row => Cslib.AffineTaylor.affineInput row node _) ?_
    rw [eqDesignRows_of_mem D f hv_sc]
    funext i
    rw [hert, List.getD_map_range _ [] v.2, ← (href.2.2.2.2.1 ⟨_, ⟨v, hv_sc⟩⟩).2.2 i]
    exact congrArg (fun a => Polynomial.ofCoeffList ((data.lookupReplacementRow a v.1).getD i.1 []))
      (val_eqScopeIndex n' eqs' f).symm
  change (List.map _ ((List.finRange eqs'.length).filter p_pred)).prod = _
  rw [hmap_eq, ← List.prod_toFinset F_jet ((List.nodup_finRange _).filter p_pred), ← map_prod]
  have hfil_set : ((List.finRange eqs'.length).filter p_pred).toFinset =
      univ.filter (fun f : Fin eqs'.length => D.factorAssign (eqScopeIndex n' eqs' f) t = g) := by
    ext f
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, Finset.mem_filter,
      Finset.mem_univ, p_pred, decide_eq_true_eq]
    rw [← val_eqScopeIndex n' eqs' f, href.2.2.2.1 (eqScopeIndex n' eqs' f) t, Fin.ext_iff]
  rw [hfil_set]

/-- At node `t`, the executable measurement fold over all decoded measurement words computes the
sum, over the `indE`-restricted Boolean cube, of the jets at `indU` of the product of formal
cleared parity factors with the design's replacement rows. -/
private theorem toJetTable_measurementFold_eq {n' Q r A₀ R J ℓ k' : ℕ} {τ : ℚ}
    {eqs' : List (List (List ℕ))} {sv ss : List (List ℕ)}
    (hr1 : 1 ≤ r) (hcan : ∀ eq ∈ eqs', IsCanonicalEquation eq)
    (hvars : ∀ eq ∈ eqs', ∀ m ∈ eq, ∀ v ∈ m, v < n')
    (hk_deg : ∀ eq ∈ eqs', ∀ m ∈ eq, m.length ≤ k')
    {data : ReplacementDesignData}
    (hdata : data = buildReplacementDesignData n' (r ^ (2 * Q)) Q r A₀ R
      (withNeutralScopesList (eqs'.map equationVars) n') sv ss)
    {D : ReplacementDesign (listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n'))
      Q r A₀ R τ}
    (href : data.Refines (withNeutralScopesList (eqs'.map equationVars) n') D)
    (t : Fin Q) (indE indU : List Bool) :
    let m_rows := data.measurementMatrix.length
    let node : ℤ := (t.1 : ℤ) + 1
    let dDen : ℤ := (commonDenom Q R : ℤ)
    let eqRowTables := buildEqRowTables n' eqs' data
    let grpEqLists := (List.range r).map fun g =>
      groupEquationsAt eqs' data.factorGroups eqRowTables t.1 g
    let measCtx : MeasStepCtx :=
      ((n', r, m_rows), (J, ℓ, k'), (node, dDen),
        (data.varGroups.getD t.1 [], data.groupMeasurementMatrices.getD t.1 []),
        (indE, indU), grpEqLists)
    CommonCountingAccum.toJetTable J ℓ
        (MeasurementFold.run measurementStepBody (r * m_rows, r ^ (2 * Q))
          (measCtx, zeroJet J ℓ)).2.2.2 =
      ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ supportOfList n' indE, x i = true),
        evalJetHom n' J ℓ (fun i => bitVal ℤ (decide (i ∈ supportOfList n' indU)))
          (∏ f : Fin eqs'.length,
            formalEqParityFactor dDen k' ℓ (eqDesignRows D f) node x
              (HeavyBranchFold.toFinsetEquation n' (eqs'[f.1]'f.isLt))) := by
  intro m_rows node dDen eqRowTables grpEqLists measCtx
  let emb := eqScopeIndex n' eqs'
  let vGroups_t := data.varGroups.getD t.1 []
  let grpMeas_t := data.groupMeasurementMatrices.getD t.1 []
  let P_eq : Fin eqs'.length → Finset (Finset (Fin n')) := fun f =>
    HeavyBranchFold.toFinsetEquation n' (eqs'[f.1]'f.isLt)
  let y_U : Fin n' → ℤ := fun i => bitVal ℤ (decide (i ∈ supportOfList n' indU))
  have hgms (g : Fin r) : (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      (grpMeas_t.getD g.1 []).length = m_rows ∧
      ∀ row ∈ grpMeas_t.getD g.1 [], row.length = (vGroups_t.getD g.1 []).length ∧
        (row.map Int.natAbs).sum ≤ r ^ (2 * Q) := by
    dsimp only [vGroups_t, grpMeas_t, m_rows]
    rw [hdata]
    exact groupMeasurementMatrices_spec (n' := n') (A₀ := A₀) (R := R)
      _ sv ss hr1 le_rfl t g
  have hVG (g : Fin r) : (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ D.varAssign v t = g :=
    ⟨(href.2.2.1 t g).1, (hgms g).1, fun v => ((href.2.2.1 t g).2.2 v).trans mem_varGroup⟩
  have hdg_eq (g : Fin r) : min (2 * n') (vGroups_t.getD g.1 []).length =
      (vGroups_t.getD g.1 []).length :=
    Nat.min_eq_right ((href.2.2.1 t g).2.1.trans (Nat.div_le_self _ _))
  have hgrp_prod (g : Fin r) (xList : List Bool) :
      CommonCountingAccum.toJetTable J ℓ
        (CommonCountingAccum.prodJet J ℓ
          ((grpEqLists.getD g.1 []).map fun eqPair =>
            evalEquationParityFactorJet J ℓ k' dDen
              (evalAffineInputZJetTable J node eqPair.2 indU xList) eqPair.1)) =
      evalJetHom n' J ℓ y_U
        (∏ f ∈ univ.filter (fun f : Fin eqs'.length => D.factorAssign (emb f) t = g),
          formalEqParityFactor dDen k' ℓ (eqDesignRows D f) node
            (fun i => xList.getD i.1 false) (P_eq f)) := by
    dsimp only [grpEqLists]
    rw [List.getD_map_range _ [] g.2]
    exact toJetTable_prodJet_groupEquationsAt hcan hvars hk_deg hdata href t g dDen node indU xList
  -- The executable fold is the shared-summary factorization of `Cslib.SharedSummaries`, with
  -- measurement map `meas`, restricted local cubes `allowed` and grouped factors `factor`.
  let meas : ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length → List ℤ := fun g ug =>
    BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 []) (List.ofFn ug)
  let allowed : ∀ g : Fin r, Finset (BitString (vGroups_t.getD g.1 []).length) := fun g =>
    univ.filter fun ug => checkRestrictedGroup n' indE (vGroups_t.getD g.1 []) (List.ofFn ug) = true
  let factor : Fin r → (∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) →
      JetTable J ℓ ℤ := fun g u =>
    evalJetHom n' J ℓ y_U
      (∏ f ∈ univ.filter (fun f : Fin eqs'.length => D.factorAssign (emb f) t = g),
        formalEqParityFactor dDen k' ℓ (eqDesignRows D f) node (localBitsEquiv hVG u) (P_eq f))
  let rep₀ : ∀ y : (Fin r → List ℤ), (∀ g, ∃ ug, meas g ug = y g) →
      ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length := fun y hy g => (hy g).choose
  let split : List ℤ → Fin r → List ℤ := fun word g => (word.drop (g.1 * m_rows)).take m_rows
  let fiber : (Fin r → List ℤ) → JetTable J ℓ ℤ :=
    SharedSummaries.fiberContribution meas allowed factor rep₀
  have hloc : ∀ g x x', (∀ h, meas h (x h) = meas h (x' h)) → x g = x' g →
      factor g x = factor g x' := fun g x x' hm hg =>
    congrArg (evalJetHom n' J ℓ y_U) (Finset.prod_congr rfl fun f hf =>
      formalEqParityFactor_congr_fiber (k' := k') (ℓ := ℓ) hdata href t hVG (emb f)
        (Finset.mem_filter.mp hf).2 (listScopeFamily_eqScopeIndex n' eqs' f).symm.subset dDen
        x x' hm hg)
  -- One step adds the fiber contribution of the measurement tuple sliced from `word`.
  have hstep (p_par : ℕ × ℕ) (word : List ℤ) (acc : JetRows) :
      (measurementStepBody ((p_par, word), (measCtx, acc))).1 = measCtx ∧
      CommonCountingAccum.toJetTable J ℓ
        (measurementStepBody ((p_par, word), (measCtx, acc))).2 =
      CommonCountingAccum.toJetTable J ℓ acc + fiber (split word) := by
    unfold measurementStepBody
    dsimp only [measCtx]
    split_ifs with hAll
    · refine ⟨rfl, ?_⟩
      rw [CommonCountingAccum.toJetTable_addJet]
      refine congrArg (CommonCountingAccum.toJetTable J ℓ acc + ·) ?_
      let repOpts : List (Option (List Bool)) := (List.range r).map fun g =>
        BooleanMeasurements.search Prod.fst Prod.snd
          ((grpMeas_t.getD g [], (word.drop (g * m_rows)).take m_rows),
            min (2 * n') (vGroups_t.getD g []).length)
      have hAll_mem (g : Fin r) : (BooleanMeasurements.search Prod.fst Prod.snd
          ((grpMeas_t.getD g.1 [], (word.drop (g.1 * m_rows)).take m_rows),
            (vGroups_t.getD g.1 []).length)).isSome = true := by
        have hm := (List.all_eq_true.mp hAll) _ (List.mem_map_of_mem (List.mem_range.mpr g.2))
        simpa only [vGroups_t, grpMeas_t, hdg_eq g] using hm
      let reps := repOpts.map fun o => o.getD []
      have hreps_spec (g : Fin r) : (reps.getD g.1 []).length = (vGroups_t.getD g.1 []).length ∧
          BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 []) (reps.getD g.1 []) =
            (word.drop (g.1 * m_rows)).take m_rows := by
        dsimp only [reps, repOpts]
        rw [List.map_map, List.getD_map_range _ [] g.2, Function.comp_apply, hdg_eq g]
        obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp (hAll_mem g)
        rw [hys, Option.getD_some]
        exact BooleanMeasurements.search_some Prod.fst Prod.snd _ hys
      let rep : ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length := fun g j =>
        (reps.getD g.1 [])[j.1]'((hreps_spec g).1.symm ▸ j.isLt)
      have hreps_ofFn (g : Fin r) : reps.getD g.1 [] = List.ofFn (rep g) :=
        List.ext_getElem ((hreps_spec g).1.trans (List.length_ofFn).symm) fun k _ _ => by
          simp only [List.getElem_ofFn, rep]
      have hrep_meas (g : Fin r) : BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 [])
          (List.ofFn (rep g)) = (word.drop (g.1 * m_rows)).take m_rows := by
        rw [← hreps_ofFn g]; exact (hreps_spec g).2
      let xStar := buildBaseAssignment n' r vGroups_t reps
      change CommonCountingAccum.toJetTable J ℓ (CommonCountingAccum.prodJet J ℓ _) = _
      rw [CommonCountingAccum.toJetTable_prodJet]
      nth_rw 1 [List.map_map]
      conv_lhs => arg 1; arg 2; rw [← List.map_coe_finRange_eq_range]
      rw [List.map_map, ← List.ofFn_eq_map, List.prod_ofFn]
      have hhdg : ∀ g : Fin r,
          min (2 * n') ((data.varGroups.getD t.1 []).getD g.1 []).length =
            (vGroups_t.getD g.1 []).length := hdg_eq
      simp only [Function.comp_apply, hhdg, CommonCountingAccum.toJetTable_streamGroupJetSum_eq_sum]
      have hy : ∀ g, ∃ ug, meas g ug = split word g := fun g => ⟨rep g, hrep_meas g⟩
      dsimp only [fiber]
      unfold SharedSummaries.fiberContribution
      rw [dite_eq_left hy]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [Finset.filter_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ug _ => ?_
      unfold evalGroupFactorJet
      dsimp only
      split_ifs with h1 h2 h2
      · rw [hgrp_prod g,
          funext (getD_applyGroupBits_buildBaseAssignment hVG rep hreps_ofFn g ug)]
        refine hloc g _ _ (fun h => ?_) (by simp only [Function.update_self])
        by_cases hhg : h = g
        · subst hhg; simp only [Function.update_self]
        · simp only [Function.update_of_ne hhg]
          exact (hrep_meas h).trans (hy h).choose_spec.symm
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        exact absurd h1 h2
      · exact absurd (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using h2) h1
      · exact CommonCountingAccum.toJetTable_zeroJet J ℓ
    · refine ⟨rfl, ?_⟩
      have hy : ¬ ∀ g, ∃ ug, meas g ug = split word g := fun hy => by
        refine hAll (List.all_eq_true.mpr fun opt hopt => ?_)
        obtain ⟨g_nat, hg_mem, rfl⟩ := List.mem_map.mp hopt
        let g : Fin r := ⟨g_nat, List.mem_range.mp hg_mem⟩
        rw [show min (2 * n') ((data.varGroups.getD t.1 []).getD g.1 []).length =
            (vGroups_t.getD g.1 []).length from hdg_eq g, Option.isSome_iff_ne_none]
        exact fun hnone => (BooleanMeasurements.search_eq_none_iff_cube Prod.fst Prod.snd _).mp
          hnone (hy g).choose (hy g).choose_spec
      dsimp only [fiber]
      unfold SharedSummaries.fiberContribution
      rw [dite_eq_right hy, add_zero]
  clear_value eqRowTables grpEqLists measCtx
  -- Fold the step over all decoded measurement words.
  rw [MeasurementFold.run_accumulator,
    foldl_fixedContext (fun st w => measurementStepBody (((r * m_rows, r ^ (2 * Q)), w), st))
      (CommonCountingAccum.toJetTable J ℓ) (fun T w => T + fiber (split w)) measCtx
      (fun acc w => hstep _ w acc),
    CommonCountingAccum.toJetTable_zeroJet, ← List.foldl_map, ← List.sum_eq_foldl, List.map_map,
    List.sum_map_range]
  -- Each local measurement is a length-`m_rows` word with entries in `[-r ^ (2Q), r ^ (2Q)]`, and
  -- only realizable tuples contribute, so the decoded words are reindexed by the measurement box.
  have hlen : ∀ g ug, (meas g ug).length = m_rows := fun g ug => by
    dsimp only [meas]; rw [BooleanMeasurements.length_evalBoolMatrix, (hgms g).2.1]
  have hbound : ∀ g ug, ∀ z ∈ meas g ug,
      -((r ^ (2 * Q) : ℕ) : ℤ) ≤ z ∧ z ≤ ((r ^ (2 * Q) : ℕ) : ℤ) := by
    intro g ug z hz
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hz
    refine abs_le.mp ?_
    rw [← Int.natCast_natAbs]
    exact Int.ofNat_le.mpr ((natAbs_evalBoolRow_le_sum row _).trans ((hgms g).2.2 row hrow).2)
  have hreal : ∀ y, fiber y ≠ 0 → ∀ g, ∃ ug, meas g ug = y g := fun y hy => by
    by_contra h
    exact hy (by dsimp only [fiber]; unfold SharedSummaries.fiberContribution; rw [dite_eq_right h])
  refine (sum_radix_eq_sum_piFinset_image meas hlen hbound fiber hreal).trans ?_
  -- Factor through the shared summaries; the local bits then form the restricted global cube.
  refine (SharedSummaries.sum_prod_eq_sum_measurement_fibers meas _
    (fun g ug => Finset.mem_image_of_mem _ (Finset.mem_univ ug)) allowed factor hloc rep₀
    fun y hy g => (hy g).choose_spec).symm.trans ?_
  rw [← sum_piFinset_checkRestrictedGroup_eq hVG indE]
  refine Finset.sum_congr rfl fun u _ => ?_
  dsimp only [factor]
  rw [← map_prod]
  exact congrArg (evalJetHom n' J ℓ y_U)
    (Finset.prod_fiberwise_of_maps_to (fun f _ => Finset.mem_univ _) _)

/-! ### 4. Restricted Subset-Pair Möbius Fold and Exact Node Taylor-Jet Identity -/

/-- At node `t`, the executable restricted subset-pair Möbius fold computes the Taylor jet at
`t + 1` of the cleared parity product of the design's scaled integer replacement rows. -/
private theorem toJetTable_subsetPairFold_eq {n' Q r A₀ R q ℓ k' : ℕ} {τ : ℚ}
    {eqs' : List (List (List ℕ))} {sv ss : List (List ℕ)}
    (hr1 : 1 ≤ r) (hcan : ∀ eq ∈ eqs', IsCanonicalEquation eq)
    (hvars : ∀ eq ∈ eqs', ∀ m ∈ eq, ∀ v ∈ m, v < n')
    (hk_deg : ∀ eq ∈ eqs', ∀ m ∈ eq, m.length ≤ k')
    {data : ReplacementDesignData}
    (hdata : data = buildReplacementDesignData n' (r ^ (2 * Q)) Q r A₀ R
      (withNeutralScopesList (eqs'.map equationVars) n') sv ss)
    {D : ReplacementDesign (listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n'))
      Q r A₀ R τ}
    (href : data.Refines (withNeutralScopesList (eqs'.map equationVars) n') D) (t : Fin Q) :
    let P_eq : Fin eqs'.length → Finset (Finset (Fin n')) := fun f =>
      HeavyBranchFold.toFinsetEquation n' (eqs'[f.1]'f.isLt)
    let J := q + 1
    let m_rows := data.measurementMatrix.length
    let node : ℤ := (t.1 : ℤ) + 1
    let dDen : ℤ := (commonDenom Q R : ℤ)
    let eqRowTables := buildEqRowTables n' eqs' data
    let grpEqLists := (List.range r).map fun g =>
      groupEquationsAt eqs' data.factorGroups eqRowTables t.1 g
    let subCtx : SubsetStepCtx :=
      ((n', r, m_rows), (r * m_rows, r ^ (2 * Q)), (J, ℓ, k'), (node, dDen),
        (data.varGroups.getD t.1 [], data.groupMeasurementMatrices.getD t.1 []), grpEqLists)
    CommonCountingAccum.toJetTable J ℓ
        (SubsetPairFold.run subsetPairStepBody n' q (subCtx, zeroJet J ℓ)).2 =
      CommonCountingAccum.taylorOuterVJet J ℓ node
        (univariateClearedParityProduct univ P_eq dDen k' ℓ
          (designReplacementScaledIntMap D (eqScopeIndex n' eqs'))) := by
  intro P_eq J m_rows node dDen eqRowTables grpEqLists subCtx
  -- `G E U` is the measurement-fold jet of the cube restricted by `E`, at the Boolean point `U`.
  let G : Finset (Fin n') → Finset (Fin n') → JetTable J ℓ ℤ := fun E U =>
    ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ E, x i = true),
      evalJetHom n' J ℓ (fun i => bitVal ℤ (decide (i ∈ U)))
        (∏ f : Fin eqs'.length, formalEqParityFactor dDen k' ℓ (eqDesignRows D f) node x (P_eq f))
  let mobBody : SubsetPairFold.DecodedPair × JetTable J ℓ ℤ → JetTable J ℓ ℤ := fun p =>
    let term := G (supportOfList n' p.1.1) (supportOfList n' p.1.2.1)
    if p.1.2.2 = true then p.2 - term else p.2 + term
  -- One step adds or subtracts the measurement-fold jet of its decoded subset pair.
  have hstep (acc : JetRows) (item : SubsetPairFold.DecodedPair) :
      (subsetPairStepBody (item, (subCtx, acc))).1 = subCtx ∧
      CommonCountingAccum.toJetTable J ℓ (subsetPairStepBody (item, (subCtx, acc))).2 =
        mobBody (item, CommonCountingAccum.toJetTable J ℓ acc) := by
    refine ⟨rfl, ?_⟩
    unfold subsetPairStepBody
    dsimp only [subCtx, mobBody]
    rw [CommonCountingAccum.toJetTable_addJet]
    have hm : CommonCountingAccum.toJetTable J ℓ
        (MeasurementFold.run measurementStepBody (r * m_rows, r ^ (2 * Q))
          (((n', r, m_rows), (J, ℓ, k'), (node, dDen),
            (data.varGroups.getD t.1 [], data.groupMeasurementMatrices.getD t.1 []),
            (item.1, item.2.1), grpEqLists), zeroJet J ℓ)).2.2.2 =
        G (supportOfList n' item.1) (supportOfList n' item.2.1) :=
      toJetTable_measurementFold_eq (J := J) (ℓ := ℓ) hr1 hcan hvars hk_deg hdata
        href t item.1 item.2.1
    cases item.2.2
    · simp only [Bool.false_eq_true, ↓reduceIte, hm]
    · simp only [↓reduceIte, CommonCountingAccum.toJetTable_smulJet, hm, neg_one_smul,
        sub_eq_add_neg]
  rw [SubsetPairFold.run_eq_foldl_map,
    foldl_fixedContext (fun st item => subsetPairStepBody (item, st))
      (CommonCountingAccum.toJetTable J ℓ) (fun T item => mobBody (item, T)) subCtx hstep,
    CommonCountingAccum.toJetTable_zeroJet, ← SubsetPairFold.run_eq_foldl_map mobBody n' q 0,
    SubsetPairFold.run_mobius_eq_sum_restricted_subsets]
  -- Compare entrywise; each entry is a Möbius sum of evaluations of a low-degree polynomial.
  apply JetTable.ext
  intro j u_col
  let p_formal : (Fin n' → Bool) → MvPolynomial (Fin n') ℤ := fun x =>
    (((∏ f : Fin eqs'.length, formalEqParityFactor dDen k' ℓ (eqDesignRows D f) node x
      (P_eq f)).coeff u_col.1).coeff j.1)
  have hlhs_entry :
      (∑ E ∈ (univ : Finset (Fin n')).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : JetTable J ℓ ℤ) ^ (#E - #U) * G E U) j u_col =
      ∑ E ∈ (univ : Finset (Fin n')).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : ℤ) ^ (#E - #U) *
          ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ E, x i = true),
            MvPolynomial.eval (fun i => bitVal ℤ (decide (i ∈ U))) (p_formal x) := by
    simp only [JetTable.sum_apply]
    refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun U _ => ?_
    rw [show (-1 : JetTable J ℓ ℤ) ^ (#E - #U) = (((-1 : ℤ) ^ (#E - #U) : ℤ) : JetTable J ℓ ℤ) by
        rw [Int.cast_pow, Int.cast_neg, Int.cast_one],
      ← zsmul_eq_mul, JetTable.coe_zsmul, smul_eq_mul]
    simp only [G, JetTable.sum_apply, evalJetHom, RingHom.comp_apply, JetTable.ofPolyVPolyZ_apply,
      Polynomial.coe_mapRingHom, Polynomial.coeff_map, p_formal]
  have hp_deg : ∀ x : Fin n' → Bool, (p_formal x).totalDegree ≤ q := fun x =>
    (totalDegree_coeff_prod_formalEqParityFactor_le univ dDen k' ℓ (eqDesignRows D) node x P_eq
      u_col.1 j.1).trans (Nat.lt_succ_iff.mp j.2)
  have hmob_eq :
      (∑ E ∈ (univ : Finset (Fin n')).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : ℤ) ^ (#E - #U) *
          ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ E, x i = true),
            MvPolynomial.eval (fun i => bitVal ℤ (decide (i ∈ U))) (p_formal x)) =
      ∑ x : Fin n' → Bool, MvPolynomial.eval (fun i => bitVal ℤ (x i)) (p_formal x) := by
    symm
    convert Cslib.BitString.sum_eval_eq_restricted_subsets q p_formal hp_deg
  rw [hlhs_entry, CommonCountingAccum.taylorOuterVJet_apply, hmob_eq]
  -- Evaluating the formal factor at a Boolean point gives the design-map factor.
  have hx_term (x : Fin n' → Bool) :
      MvPolynomial.eval (fun i => bitVal ℤ (x i)) (p_formal x) =
      ((∏ f : Fin eqs'.length, parityFactorCleared ℓ (Polynomial.C (dDen ^ k'))
        (clearedMonomialSumPoly dDen k'
          (fun v => Polynomial.taylor node (designReplacementScaledIntMap D (eqScopeIndex n' eqs')
            x f v))
          (P_eq f))).coeff u_col.1).coeff j.1 := by
    dsimp only [p_formal]
    rw [← Polynomial.coeff_map, ← Polynomial.coe_mapRingHom, ← Polynomial.coeff_map,
      Polynomial.map_prod]
    refine congrArg (fun P : Polynomial (Polynomial ℤ) => (P.coeff u_col.1).coeff j.1)
      (Finset.prod_congr rfl fun f _ => ?_)
    simp only [Polynomial.coe_mapRingHom, formalEqParityFactor,
      map_parityFactorCleared (Polynomial.mapRingHom (MvPolynomial.eval fun i => bitVal ℤ (x i))),
      Polynomial.map_C, MvPolynomial.eval_C]
    apply congrArg (parityFactorCleared ℓ _)
    rw [formalClearedMonomialSum, Polynomial.map_sum, clearedMonomialSumPoly]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.eval_C, Polynomial.map_prod,
      clearedMonomialPoly]
    apply congrArg (_ * ·)
    refine Finset.prod_congr rfl fun v hvM => ?_
    have hv_sc : v ∈ listScopeFamily n' (withNeutralScopesList (eqs'.map equationVars) n')
        (eqScopeIndex n' eqs' f) := by
      rw [listScopeFamily_eqScopeIndex]
      exact Finset.mem_biUnion.mpr ⟨M, hM, hvM⟩
    rw [Cslib.AffineTaylor.map_eval_self_affineInput,
      designReplacementScaledIntMap_of_mem D _ x hv_sc, eqDesignRows_of_mem D f hv_sc]
    exact congrArg (Polynomial.taylor node) (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  rw [Finset.sum_congr rfl fun x _ => hx_term x]
  -- The Boolean sum of coefficients is the coefficient of the cleared parity coordinate.
  change (∑ x : Fin n' → Bool, Polynomial.lcoeff ℤ j.1 _) = _
  rw [← map_sum, ← univariateClearedParityCoord_eq_sum, ← taylor_univariateClearedParityCoord]
  rfl

/-- Clearing a nonzero integer denominator `Ω` from the rational Taylor jet of `Ω⁻¹ • H`
recovers the integer Taylor jet of `H`. -/
private theorem zsmul_taylorOuterVJet_map_mul_inv {J ℓ : ℕ} (node Ω : ℤ) (hΩ : Ω ≠ 0)
    (H : Polynomial (Polynomial ℤ)) :
    Ω • CommonCountingAccum.taylorOuterVJet J ℓ (node : ℚ)
        (H.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) *
          Polynomial.C (Polynomial.C ((Ω : ℚ)⁻¹))) =
      JetTable.castRingHom ℚ (CommonCountingAccum.taylorOuterVJet J ℓ node H) := by
  apply JetTable.ext
  intro j u
  have hnode : (node : ℚ) = Int.castRingHom ℚ node := rfl
  simp only [JetTable.coe_zsmul, zsmul_eq_mul, JetTable.castRingHom_apply,
    CommonCountingAccum.taylorOuterVJet_apply, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    Polynomial.coe_mapRingHom]
  rw [hnode, Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.coeff_mul_C,
    ← Polynomial.map_taylor, Polynomial.coeff_map, Int.coe_castRingHom, ← mul_assoc,
    mul_comm (Ω : ℚ), mul_assoc, mul_inv_cancel₀ (Int.cast_ne_zero.mpr hΩ), mul_one]

end Stage2Exactness

/-! ### 5. Exact Root-Count Recovery (`evalBoundedIncidenceBranch_eq_rootCount`) -/

/-- **Proposition 5.3 exact root-count correctness**
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§5.3–5.5, Proposition 5.3,
pp. 37–39): whenever a reduced system `(n', eqs')` passes `checkBranchFeasible N₀_branch`,
`evalBoundedIncidenceBranch (prepareBranchEvalInput (n', eqs'))` equals
`HeavyBranchFold.rootCount n' eqs'`. -/
theorem evalBoundedIncidenceBranch_eq_rootCount {N₀_branch n' : ℕ}
    {eqs' : List (List (List ℕ))}
    (hfeas : checkBranchFeasible N₀_branch (n', eqs') = true) :
    evalBoundedIncidenceBranch (prepareBranchEvalInput (n', eqs')) =
      HeavyBranchFold.rootCount n' eqs' := by
  have hvalid := validBranchEvalParams_prepare_of_feasible hfeas
  have hf_all := feasible_of_checkBranchFeasible hfeas
  dsimp only [prepareBranchEvalInput] at hf_all
  obtain ⟨_, hcan, hvars, hF⟩ := hf_all
  have href_ex := exists_refines_prepare_of_feasible hfeas
  dsimp only [prepareBranchEvalInput, ParameterCheck.computeScheduleParams] at href_ex
  obtain ⟨hQn, hRn, hrn, hA₀n, haux, hshape, D, href, _, hrmeas_le⟩ := href_ex
  let b := branchMaxFactorIncidence n' eqs'; let w := branchMaxFactorWidth n' eqs'
  let β := ParameterCheck.chooseBeta (Nat.clog 2 n') b w
  let r := ReplacementParams.numGroups n'; let Q := ReplacementParams.numNodes n'
  let R := ReplacementParams.rowBound β n'; let A₀ := ReplacementParams.intervalStart β n'
  let k' := sysMaxDegree eqs'
  have hr2 : 2 ≤ r := hF.two_le_numGroups; have hr1 : 1 ≤ r := by omega
  have hRQ : R < Q := hF.rowBound_lt_numNodes; have hQ_pos : 0 < Q := by omega
  have hmaxQ : max 1 (ReplacementParams.numNodes n') = ReplacementParams.numNodes n' :=
    Nat.max_eq_right (by omega)
  let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
  let edges := scopeIncidencesList n' augScopes
  let scheds := BalancedSchedules.constructBalancedSchedules
    n' augScopes.length Q r (b + w) edges
  let data := buildReplacementDesignData n' (r ^ (2 * Q)) Q r A₀ R augScopes scheds.1 scheds.2
  rw [Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
    Nat.min_eq_right hA₀n, Nat.min_eq_right haux] at hshape href hrmeas_le
  have hshape' : validDesignShape n' r eqs'.length data = true := hshape
  have href' : data.Refines augScopes D := href
  have hc_meas : min (4 * (n' + 1) * (eqs'.length * n' + n' + 1))
      (r * data.measurementMatrix.length) = r * data.measurementMatrix.length :=
    Nat.min_eq_right (hrmeas_le.trans
      ((by omega : n' ≤ eqs'.length * n' + n' + 1).trans (Nat.le_mul_of_pos_left _ (by omega))))
  unfold evalBoundedIncidenceBranch
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  dsimp only [prepareBranchEvalInput, ParameterCheck.computeScheduleParams]
  simp only [Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
    Nat.min_eq_right hA₀n, Nat.min_eq_right haux, hmaxQ]
  change (if !validDesignShape n' r eqs'.length data then 0 else _) = _
  simp only [hshape', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hc_meas, href'.2.1]
  let ℓ := n' + 1; let q := (k' * (R - 1)) * (eqs'.length + 2 * n') / Q; let J := q + 1
  let dDen : ℤ := (commonDenom Q R : ℤ); let Ω : ℤ := ((dDen ^ k') ^ (2 * ℓ - 1)) ^ eqs'.length
  let nodes : List ℤ := (List.range Q).map fun (t : ℕ) => ((t : ℤ) + 1)
  let eqRowTables := buildEqRowTables n' eqs' data
  let nodeJets : List JetRows := (List.range Q).map fun (t : ℕ) =>
    let node : ℤ := (t : ℤ) + 1
    let grpEqLists := (List.range r).map fun g =>
      groupEquationsAt eqs' data.factorGroups eqRowTables t g
    let subCtx : SubsetStepCtx :=
      ((n', r, data.measurementMatrix.length),
        (r * data.measurementMatrix.length, r ^ (2 * Q)), (J, ℓ, k'), (node, dDen),
        (data.varGroups.getD t [], data.groupMeasurementMatrices.getD t []), grpEqLists)
    (SubsetPairFold.run subsetPairStepBody n' q (subCtx, zeroJet J ℓ)).2
  change min (2 ^ n') (CommonCountingAccum.recoverOuterJetSumModPowTwo nodes J ℓ Ω nodeJets).toNat =
    HeavyBranchFold.rootCount n' eqs'
  let emb := eqScopeIndex n' eqs'
  let P_eq : Fin eqs'.length → Finset (Finset (Fin n')) := fun f =>
    HeavyBranchFold.toFinsetEquation n' eqs'[f]
  have hk_list : ∀ eq ∈ eqs', ∀ m ∈ eq, m.length ≤ k' := fun _ heq _ hm =>
    length_mem_le_sysMaxDegree heq hm
  have hk_fin : ∀ f ∈ (univ : Finset (Fin eqs'.length)), ∀ M ∈ P_eq f, #M ≤ k' := by
    intro f _ M hM
    simp only [P_eq, HeavyBranchFold.toFinsetEquation, List.mem_toFinset, List.mem_map] at hM
    obtain ⟨m, hm, rfl⟩ := hM
    have hcard_le : #(univ.filter fun i : Fin n' => i.1 ∈ m) ≤ #(m.toFinset) := by
      rw [← Finset.card_image_of_injective _ Fin.val_injective]
      refine Finset.card_le_card fun w hw => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
    exact hcard_le.trans ((List.toFinset_card_le m).trans
      (hk_list eqs'[f] (List.getElem_mem f.2) m hm))
  have hΩ_eq : Ω = clearedProductDenom dDen k' ℓ #(univ : Finset (Fin eqs'.length)) := by
    simp only [Ω, clearedProductDenom, Finset.card_univ, Fintype.card_fin]
  have hΩ_ne : Ω ≠ 0 := hΩ_eq ▸ clearedProductDenom_ne_zero (commonDenom_intCast_ne_zero Q R)
    k' ℓ _
  let H_tilde := univariateClearedParityProduct univ P_eq dDen k' ℓ
    (designReplacementScaledIntMap D emb)
  let P_rat : Polynomial (Polynomial ℚ) :=
    H_tilde.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) *
      Polynomial.C (Polynomial.C ((Ω : ℚ)⁻¹))
  let H_zero : Fin ℓ → ℤ := fun u => (H_tilde.coeff u.1).eval 0 / Ω
  have hnodes_nodup : nodes.Nodup :=
    List.Nodup.map (fun a b h => by omega) List.nodup_range
  have hlen_nj : nodeJets.length = nodes.length := by
    simp only [nodeJets, nodes, List.length_map, List.length_range]
  have hclear : ∀ i : Fin nodes.length,
      Ω • CommonCountingAccum.taylorOuterVJet J ℓ ((nodes[i.1]'i.isLt : ℤ) : ℚ) P_rat =
        JetTable.castRingHom ℚ
          (CommonCountingAccum.toJetTable J ℓ (nodeJets[i.1]'(hlen_nj.symm ▸ i.isLt))) := by
    intro i
    have hi_Q : i.1 < Q := by simpa only [nodes, List.length_map, List.length_range] using i.2
    let t : Fin Q := ⟨i.1, hi_Q⟩
    have hnj_t : CommonCountingAccum.toJetTable J ℓ (nodeJets[i.1]'(hlen_nj.symm ▸ i.isLt)) =
        CommonCountingAccum.taylorOuterVJet J ℓ ((t.1 : ℤ) + 1) H_tilde := by
      simp only [nodeJets, List.getElem_map, List.getElem_range]
      exact toJetTable_subsetPairFold_eq hr1 hcan hvars hk_list rfl href' t
    have hni : (nodes[i.1]'i.isLt : ℤ) = (t.1 : ℤ) + 1 := by
      simp only [nodes, List.getElem_map, List.getElem_range, t]
    rw [hnj_t, hni]
    exact zsmul_taylorOuterVJet_map_mul_inv _ Ω hΩ_ne H_tilde
  clear_value scheds edges data eqRowTables nodeJets
  have hdeg : ∀ u : Fin ℓ, (P_rat.coeff u.1).natDegree < nodes.length * J := by
    intro u
    have hP_coeff : P_rat.coeff u.1 =
        (H_tilde.coeff u.1).map (Int.castRingHom ℚ) * Polynomial.C ((Ω : ℚ)⁻¹) := by
      simp only [P_rat, Polynomial.coeff_mul_C, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    have hle1 : (P_rat.coeff u.1).natDegree ≤ (H_tilde.coeff u.1).natDegree := by
      rw [hP_coeff]
      exact (Polynomial.natDegree_mul_le).trans (by
        rw [Polynomial.natDegree_C, add_zero]; exact Polynomial.natDegree_map_le)
    have hle2 : (H_tilde.coeff u.1).natDegree ≤ (k' * (R - 1)) * (eqs'.length + 2 * n') := by
      have hd := natDegree_univariateClearedParityCoord_design_le D emb univ P_eq hk_fin u.2
      simpa only [H_tilde, univariateClearedParityCoord, Finset.card_univ, Fintype.card_fin, ℓ,
        Nat.add_sub_cancel] using hd
    have hlt_QJ : (k' * (R - 1)) * (eqs'.length + 2 * n') < Q * J := by
      dsimp only [J, q]
      have hdm := Nat.div_add_mod ((k' * (R - 1)) * (eqs'.length + 2 * n')) Q
      have hmod := Nat.mod_lt ((k' * (R - 1)) * (eqs'.length + 2 * n')) hQ_pos
      rw [Nat.mul_succ]; omega
    have hnl : nodes.length = Q := by simp only [nodes, List.length_map, List.length_range]
    rw [hnl]
    exact (hle1.trans hle2).trans_lt hlt_QJ
  have hH0 : ∀ u : Fin ℓ, (P_rat.coeff u.1).eval 0 = (H_zero u : ℚ) := by
    intro u
    have hdvd_u : Ω ∣ (H_tilde.coeff u.1).eval 0 := by
      rw [hΩ_eq]
      exact dvd_eval_zero_univariateClearedParityCoord univ P_eq dDen (by omega : 1 ≤ ℓ)
        (designReplacementScaledIntMap D emb) hk_fin
        (fun x f _ _ _ v _ => eval_zero_designReplacementScaledIntMap D emb x f v) u.1
    have hmul_div : Ω * H_zero u = (H_tilde.coeff u.1).eval 0 := Int.mul_ediv_cancel' hdvd_u
    have hΩq_ne : (Ω : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hΩ_ne
    have h0q : (0 : ℚ) = Int.castRingHom ℚ 0 := rfl
    simp only [P_rat, Polynomial.coeff_mul_C, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
      Polynomial.eval_mul, Polynomial.eval_C]
    rw [h0q, Polynomial.eval_map_apply, Int.coe_castRingHom, ← hmul_div]
    dsimp only
    rw [Int.cast_mul, mul_comm (Ω : ℚ), mul_assoc, mul_inv_cancel₀ hΩq_ne, mul_one]
  let count : ℤ := (HeavyBranchFold.rootCount n' eqs' : ℤ)
  have hrc_le : HeavyBranchFold.rootCount n' eqs' ≤ 2 ^ n' :=
    HeavyBranchFold.rootCount_le_two_pow n' eqs'
  have hcount₀ : 0 ≤ count := Nat.cast_nonneg _
  have hcount₁ : count < (2 : ℤ) ^ ℓ := by
    have hpow_lt : 2 ^ n' < 2 ^ ℓ := Nat.pow_lt_pow_right (by omega) (by dsimp only [ℓ]; omega)
    dsimp only [count]
    exact_mod_cast hrc_le.trans_lt hpow_lt
  have hdvd : (2 : ℤ) ^ ℓ ∣ (∑ u : Fin ℓ, H_zero u) - count := by
    have hmod_eq := emod_sum_ediv_eval_zero_clearedParityCoord_design_eq_commonZeroCount D emb univ
      P_eq (by dsimp only [ℓ]; omega : n' < ℓ) hk_fin
    rw [← hΩ_eq, ← HeavyBranchFold.rootCount_eq_commonZeroCount hcan hvars] at hmod_eq
    have hsum_range : (∑ u : Fin ℓ, H_zero u) =
        ∑ s ∈ Finset.range ℓ, (H_tilde.coeff s).eval 0 / Ω :=
      Fin.sum_univ_eq_sum_range (fun s => (H_tilde.coeff s).eval 0 / Ω) ℓ
    change (∑ s ∈ Finset.range ℓ, (H_tilde.coeff s).eval 0 / Ω) % (2 : ℤ) ^ ℓ = count at hmod_eq
    rw [← hsum_range] at hmod_eq
    have hedm := Int.mul_ediv_add_emod (∑ u : Fin ℓ, H_zero u) ((2 : ℤ) ^ ℓ)
    exact ⟨(∑ u : Fin ℓ, H_zero u) / (2 : ℤ) ^ ℓ, by omega⟩
  have hrec := CommonCountingAccum.recoverOuterJetSumModPowTwo_eq hnodes_nodup hΩ_ne nodeJets
    hlen_nj P_rat H_zero hclear hdeg hH0 hcount₀ hcount₁ hdvd
  rw [hrec, Int.toNat_natCast, Nat.min_eq_right hrc_le]

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
