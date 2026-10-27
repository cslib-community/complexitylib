/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
import all Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact root-count correctness for the bounded-incidence branch evaluator (Proposition 5.3)

Proves the Stage-2 measurement-fiber Taylor-jet equivalence and Hermite–Cramer modular recovery
theorem `evalBoundedIncidenceBranch_eq_rootCount` for the executable bounded-incidence branch
evaluator `evalBoundedIncidenceBranch` from
`Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics`, formalizing the
semantic correctness half of Proposition 5.3 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (§§3.4–3.5, §4.6, §§5.3–5.5,
Proposition 5.3, and Appendix B.2–B.3, pp. 24–26, 33–34, 37–39, 48–50).

Exactness holds on feasible prepared inputs (`prepareBranchEvalInput (n', eqs')` when
`checkBranchFeasible N₀_branch (n', eqs') = true`). Invalid raw `BranchEvalInput` tuples fail
`validBranchEvalParams` or the unary resource-dimension guard `validDesignShape` (which bounds
measurement and group dimensions rather than certifying arbitrary designs) and return `0`.

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
        intro _
        rw [Finset.sum_empty, MvPolynomial.totalDegree_zero]
        exact Nat.zero_le j
      | cons ab s hab ih =>
        intro hs
        rw [Finset.sum_cons]
        have hab_eq : ab.1 + ab.2 = j := hs ab (Finset.mem_cons_self ab s)
        have h1 := hP ab.1
        have h2 := hQ ab.2
        have hmul : (P.coeff ab.1 * Q.coeff ab.2).totalDegree ≤ j :=
          (MvPolynomial.totalDegree_mul _ _).trans (by omega)
        exact (MvPolynomial.totalDegree_add _ _).trans
          (max_le hmul (ih fun x hx => hs x (Finset.mem_cons_of_mem hx)))
    exact hsum_deg _ fun _ hab => Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  one_mem' j := by
    by_cases hj : j = 0
    · subst hj
      simp only [Polynomial.coeff_one_zero, MvPolynomial.totalDegree_one, le_rfl]
    · simp only [Polynomial.coeff_one, hj, ↓reduceIte, MvPolynomial.totalDegree_zero, Nat.zero_le]
  add_mem' {P Q} hP hQ j := by
    rw [Polynomial.coeff_add]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hP j) (hQ j))
  zero_mem' j := by
    simp only [Polynomial.coeff_zero, MvPolynomial.totalDegree_zero, Nat.zero_le]
  neg_mem' {P} hP j := by
    rw [Polynomial.coeff_neg, MvPolynomial.totalDegree_neg]
    exact hP j

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
  have hinj_img : Function.Injective (Finset.image (Fin.val : Fin n' → ℕ)) := fun A B h => by
    ext i; refine ⟨fun hi => ?_, fun hi => ?_⟩
    · obtain ⟨a, ha, ha_eq⟩ := Finset.mem_image.mp (h ▸ Finset.mem_image_of_mem Fin.val hi)
      exact Fin.ext ha_eq ▸ ha
    · obtain ⟨b, hb, hb_eq⟩ := Finset.mem_image.mp (h.symm ▸ Finset.mem_image_of_mem Fin.val hi)
      exact Fin.ext hb_eq ▸ hb
  have himg_m : ∀ m ∈ eq,
      Finset.image Fin.val ({i : Fin n' | i.1 ∈ m} : Finset (Fin n')) = m.toFinset := by
    intro m hm; ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    refine ⟨?_, fun hw => ⟨⟨w, hvars m hm w hw⟩, hw, rfl⟩⟩
    rintro ⟨i, hi, rfl⟩; exact hi
  have heq_img : (eq.map List.toFinset).toFinset =
      (HeavyBranchFold.toFinsetEquation n' eq).image (Finset.image Fin.val) := by
    ext S
    simp only [HeavyBranchFold.toFinsetEquation, Finset.mem_image, List.mem_toFinset, List.mem_map]
    refine ⟨?_, ?_⟩
    · rintro ⟨m, hm, rfl⟩; exact ⟨_, ⟨m, hm, rfl⟩, himg_m m hm⟩
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩; exact ⟨m, hm, (himg_m m hm).symm⟩
  have hsum_eq : clearedMonomialSumPoly dDen k' θ (eq.map List.toFinset).toFinset =
      (formalClearedMonomialSum dDen k'
        (fun v => Cslib.AffineTaylor.affineInput (rowsNat v.1) node x)
        (HeavyBranchFold.toFinsetEquation n' eq)).map (MvPolynomial.eval y) := by
    rw [clearedMonomialSumPoly, heq_img, Finset.sum_image (fun _ _ _ _ h => hinj_img h),
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
  rw [List.length_map]
  have hfn : List.map
      (fun j => if (List.ofFn ug).getD j false = true then
        (Vg.map fun v => row.getD v 0).getD j 0 else 0) (List.range Vg.length) =
      List.ofFn (fun j : Fin Vg.length => row.getD Vg[j] 0 * bitVal ℤ (ug j)) := by
    refine List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_ofFn])
      fun k _ hk2 => ?_
    have hk : k < Vg.length := by simpa only [List.length_ofFn] using hk2
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      List.getD_eq_getElem (List.ofFn ug) false (by simp only [List.length_ofFn]; exact hk),
      List.getElem_ofFn, List.getD_eq_getElem _ 0 (by simp only [List.length_map]; exact hk),
      List.getElem_map]
    cases ug ⟨k, hk⟩ <;> simp only [bitVal, mul_zero, mul_one, ↓reduceIte, Bool.false_eq_true,
      Fin.getElem_fin]
  rw [hfn, List.sum_ofFn]

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
    (rep u : ∀ h : Fin r, BitString ((data.varGroups.getD t.1 []).getD h.1 []).length)
    (hmeas_eq : ∀ h : Fin r,
      BooleanMeasurements.evalBoolMatrix ((data.groupMeasurementMatrices.getD t.1 []).getD h.1 [])
        (List.ofFn (rep h)) =
      BooleanMeasurements.evalBoolMatrix ((data.groupMeasurementMatrices.getD t.1 []).getD h.1 [])
        (List.ofFn (u h))) :
    let scope := listScopeFamily n' augScopes
    let rows : Fin n' → Fin n' → Polynomial ℤ := fun v i =>
      if hv : v ∈ scope f_aug then
        varReplacementRowScaledInt Q r A₀ R D.place (BalancedSchedules.scopeVarOf scope)
          ⟨f_aug, ⟨v, hv⟩⟩ i
      else 0
    formalEqParityFactor dDen k' ℓ rows ((t.1 : ℤ) + 1)
        (localBitsEquiv hVG (Function.update rep g (u g))) 𝓜 =
      formalEqParityFactor dDen k' ℓ rows ((t.1 : ℤ) + 1) (localBitsEquiv hVG u) 𝓜 := by
  intro scope rows
  subst hfg
  let g := D.factorAssign f_aug t
  let u' := Function.update rep g (u g)
  let x₁ := localBitsEquiv hVG u'
  let x₂ := localBitsEquiv hVG u
  have hu'_meas : ∀ h : Fin r,
      BooleanMeasurements.evalBoolMatrix ((data.groupMeasurementMatrices.getD t.1 []).getD h.1 [])
        (List.ofFn (u' h)) =
      BooleanMeasurements.evalBoolMatrix ((data.groupMeasurementMatrices.getD t.1 []).getD h.1 [])
        (List.ofFn (u h)) := fun h => by
    dsimp only [u']
    by_cases hhg : h = g
    · subst hhg; rw [Function.update_self]
    · rw [Function.update_of_ne hhg]; exact hmeas_eq h
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
        rw [List.map_map, getD_map_range _ [] t.2, Function.comp_apply, List.map_map,
          getD_map_range _ [] h.2, Function.comp_apply,
          getD_map_range _ [] t.2, getD_map_range _ [] h.2]
      have hget := congrArg (fun L : List ℤ => L.getD idx 0) (hCth ▸ hu'_meas h)
      dsimp only [BooleanMeasurements.evalBoolMatrix, CopyPlacement.restrictGroupColumns] at hget
      have hlen1 : idx < (List.map (fun r_sub => BooleanMeasurements.evalBoolRow r_sub
          (List.ofFn (u' h))) (List.map (fun r0 => List.map (fun v => r0.getD v 0)
            ((data.varGroups.getD t.1 []).getD h.1 [])) data.measurementMatrix)).length := by
        simpa only [List.length_map] using hidx
      have hlen2 : idx < (List.map (fun r_sub => BooleanMeasurements.evalBoolRow r_sub
          (List.ofFn (u h))) (List.map (fun r0 => List.map (fun v => r0.getD v 0)
            ((data.varGroups.getD t.1 []).getD h.1 [])) data.measurementMatrix)).length := by
        simpa only [List.length_map] using hidx
      rw [List.getD_eq_getElem _ 0 hlen1, List.getD_eq_getElem _ 0 hlen2,
        List.getElem_map, List.getElem_map, List.getElem_map, List.getElem_map] at hget
      exact hget
    have hbit : ∀ b : Bool, ((bitVal ℤ b : ℤ) : ℚ) = bitVal ℚ b := fun b => by cases b <;> rfl
    have hq_eq : (∑ i : Fin n', (data.measurementMatrix[idx].getD i.1 0 : ℚ) * bitVal ℚ (x₁ i)) =
        (∑ i : Fin n', (data.measurementMatrix[idx].getD i.1 0 : ℚ) * bitVal ℚ (x₂ i)) := by
      simpa only [Int.cast_sum, Int.cast_mul, hbit] using congrArg (Int.cast : ℤ → ℚ) hint_eq
    simp only [mul_sub, Finset.sum_sub_distrib, hq_eq, sub_self]
  have hgrp : ∀ w ∈ varGroup D.varAssign t g, x₁ w = x₂ w := fun w hw => by
    have hwg : g = D.varAssign w t := (mem_varGroup.mp hw).symm
    dsimp only [x₁, x₂]
    rw [localBitsEquiv_apply hVG, localBitsEquiv_apply hVG]
    dsimp only [u']
    rw [hwg, Function.update_self]
  unfold formalEqParityFactor formalClearedMonomialSum
  congr 1; refine Finset.sum_congr rfl fun M hM => ?_
  congr 1; refine Finset.prod_congr rfl fun v hvM => ?_
  have hv_sc : v ∈ scope f_aug := hscope (Finset.mem_biUnion.mpr ⟨M, hM, hvM⟩)
  let e : BalancedSchedules.ScopeIncidence scope := ⟨f_aug, ⟨v, hv_sc⟩⟩
  have hrows_v : rows v =
      varReplacementRowScaledInt Q r A₀ R D.place (BalancedSchedules.scopeVarOf scope) e := by
    funext i; simp only [rows, hv_sc, ↓reduceDIte]; rfl
  dsimp only
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
  have heval_sum : ∀ x : Fin n' → Bool,
      (evalVarReplacementRowScaledIntPoly D e x).eval ((t.1 : ℤ) + 1) =
        ∑ i : Fin n', (varReplacementRowScaledInt Q r A₀ R D.place
          (BalancedSchedules.scopeVarOf scope) e i).eval ((t.1 : ℤ) + 1) * bitVal ℤ (x i) := by
    intro x
    dsimp only [evalVarReplacementRowScaledIntPoly]
    change Polynomial.evalRingHom ((t.1 : ℤ) + 1) (∑ i, _) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    change (Polynomial.C (bitVal ℤ (x i))).eval ((t.1 : ℤ) + 1) *
      (varReplacementRowScaledInt Q r A₀ R D.place (BalancedSchedules.scopeVarOf scope) e i).eval
        ((t.1 : ℤ) + 1) = _
    rw [Polynomial.eval_C, mul_comm]
  rwa [heval_sum x₁, heval_sum x₂] at hint_eval

/-! ### 3. Measurement-Tuple Coverage and Two-Pass Fiber Jet Fold Equivalence -/

private theorem sliceBlocks_iff_eq_flatten {r m : ℕ} (L : Fin r → List ℤ)
    (hL : ∀ g : Fin r, (L g).length = m) {word : List ℤ} (hw : word.length = r * m) :
    (∀ g : Fin r, (word.drop (g.1 * m)).take m = L g) ↔ word = (List.ofFn L).flatten := by
  induction r generalizing word with
  | zero =>
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at hw
    subst hw
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
          have hg := h g.succ
          have hmul : g.succ.1 * m = m + g.1 * m := by rw [Fin.val_succ, Nat.succ_mul, add_comm]
          rwa [hmul, ← List.drop_drop] at hg
      rw [← List.take_append_drop m word, h0, hrest]
    · have happ : word.take m ++ word.drop m =
          L 0 ++ (List.ofFn fun i : Fin r => L i.succ).flatten := by
        rwa [List.take_append_drop]
      obtain ⟨h0, hrest⟩ := List.append_inj happ (htake_len.trans (hL 0).symm)
      refine Fin.cases ?_ (fun g' => ?_) g
      · simpa only [Fin.val_zero, Nat.zero_mul, List.drop_zero] using h0
      · have hmul : g'.succ.1 * m = m + g'.1 * m := by rw [Fin.val_succ, Nat.succ_mul, add_comm]
        rw [hmul, ← List.drop_drop]
        exact (ih (fun i => L i.succ) (fun i => hL i.succ) hdrop_len).mpr hrest g'

private theorem natAbs_evalBoolRow_le_sum (row : List ℤ) (bs : List Bool) :
    (BooleanMeasurements.evalBoolRow row bs).natAbs ≤ (row.map Int.natAbs).sum := by
  unfold BooleanMeasurements.evalBoolRow
  have hrow : row = (List.range row.length).map fun j => row.getD j 0 :=
    List.ext_getElem (by simp only [List.length_map, List.length_range]) fun j hj _ => by
      simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem row 0 hj]
  conv_rhs => rw [hrow, List.map_map]
  have hpt : ∀ js : List ℕ,
      ((js.map fun j => if bs.getD j false = true then row.getD j 0 else 0).sum).natAbs ≤
      (js.map (Int.natAbs ∘ fun j => row.getD j 0)).sum := by
    intro js
    induction js with
    | nil => exact le_rfl
    | cons j js ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      refine (Int.natAbs_add_le _ _).trans (Nat.add_le_add ?_ ih)
      cases bs.getD j false <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_zero, Nat.zero_le, le_rfl]
  exact hpt (List.range row.length)

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
    let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
    let scope := listScopeFamily n' augScopes
    let emb : Fin eqs'.length → Fin augScopes.length := fun f =>
      withNeutralScopesIndexEquiv (eqs'.map equationVars) n'
        (Sum.inl ⟨f.1, by simp only [List.length_map]; exact f.2⟩)
    let designRows : Fin eqs'.length → Fin n' → Fin n' → Polynomial ℤ := fun f v i =>
      if hv : v ∈ scope (emb f) then
        varReplacementRowScaledInt Q r A₀ R D.place (BalancedSchedules.scopeVarOf scope)
          ⟨emb f, ⟨v, hv⟩⟩ i
      else 0
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
            formalEqParityFactor dDen k' ℓ (designRows f) node x
              (HeavyBranchFold.toFinsetEquation n' eqs'[f])) := by
  intro augScopes scope emb designRows m_rows node dDen eqRowTables grpEqLists measCtx
  let vGroups_t := data.varGroups.getD t.1 []
  let grpMeas_t := data.groupMeasurementMatrices.getD t.1 []
  let P_eq : Fin eqs'.length → Finset (Finset (Fin n')) := fun f =>
    HeavyBranchFold.toFinsetEquation n' eqs'[f]
  let y_U : Fin n' → ℤ := fun i => bitVal ℤ (decide (i ∈ supportOfList n' indU))
  have hy_U_eq : (fun i : Fin n' => bitVal ℤ (indU.getD i.1 false)) = y_U := by
    funext i; congr 1; apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, mem_supportOfList]
  have hemb_val : ∀ f : Fin eqs'.length, (emb f).1 = f.1 := fun f => by
    simp only [emb, withNeutralScopesIndexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finSumFinEquiv_apply_left, Fin.val_castAdd]
  have hscope_eq : ∀ f : Fin eqs'.length, scope (emb f) = equationScope (P_eq f) := fun f => by
    dsimp only [scope, emb, P_eq]
    rw [listScopeFamily_withNeutralScopesList]
    dsimp only [withNeutralScope]
    exact listScopeFamily_map_equationVars n' eqs' f
  have hgms : ∀ g : Fin r, (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      (grpMeas_t.getD g.1 []).length = m_rows ∧
      ∀ row ∈ grpMeas_t.getD g.1 [], row.length = (vGroups_t.getD g.1 []).length ∧
        (row.map Int.natAbs).sum ≤ r ^ (2 * Q) := fun g => by
    dsimp only [vGroups_t, grpMeas_t, m_rows]
    rw [hdata]
    exact groupMeasurementMatrices_spec (n' := n') (A₀ := A₀) (R := R)
      augScopes sv ss hr1 le_rfl t g
  have hVG : ∀ g : Fin r, (vGroups_t.getD g.1 []).Nodup ∧ (∀ w ∈ vGroups_t.getD g.1 [], w < n') ∧
      ∀ v : Fin n', v.1 ∈ vGroups_t.getD g.1 [] ↔ D.varAssign v t = g := fun g =>
    ⟨(href.2.2.1 t g).1, (hgms g).1, fun v => ((href.2.2.1 t g).2.2 v).trans mem_varGroup⟩
  have hdg_eq : ∀ g : Fin r, min (2 * n') (vGroups_t.getD g.1 []).length =
      (vGroups_t.getD g.1 []).length := fun g =>
    Nat.min_eq_right ((href.2.2.1 t g).2.1.trans (Nat.div_le_self _ _))
  have hgrp_prod : ∀ (g : Fin r) (xList : List Bool),
      CommonCountingAccum.toJetTable J ℓ
        (CommonCountingAccum.prodJet J ℓ
          ((grpEqLists.getD g.1 []).map fun eqPair =>
            evalEquationParityFactorJet J ℓ k' dDen
              (evalAffineInputZJetTable J node eqPair.2 indU xList) eqPair.1)) =
      evalJetHom n' J ℓ y_U
        (∏ f ∈ univ.filter (fun f : Fin eqs'.length => D.factorAssign (emb f) t = g),
          formalEqParityFactor dDen k' ℓ (designRows f) node
            (fun i => xList.getD i.1 false) (P_eq f)) := by
    intro g xList
    rw [CommonCountingAccum.toJetTable_prodJet]
    dsimp only [grpEqLists]
    rw [getD_map_range _ [] g.2]
    unfold groupEquationsAt
    have hrange_fin : List.range eqs'.length = (List.finRange eqs'.length).map Fin.val := by
      refine List.ext_getElem (by simp only [List.length_range, List.length_map,
        List.length_finRange]) fun k hk _ => ?_
      simp only [List.getElem_range, List.getElem_map, List.getElem_finRange, Fin.val_cast]
    rw [hrange_fin, List.filter_map, List.map_map, List.map_map, List.map_map]
    let p_pred : Fin eqs'.length → Bool := fun f =>
      decide ((data.factorGroups.getD f.1 []).getD t.1 0 = g.1)
    let F_jet : Fin eqs'.length → JetTable J ℓ ℤ := fun f =>
      evalJetHom n' J ℓ y_U (formalEqParityFactor dDen k' ℓ (designRows f) node
        (fun i => xList.getD i.1 false) (P_eq f))
    have hmap_eq : List.map
        (((CommonCountingAccum.toJetTable J ℓ ∘ fun eqPair : List (List ℕ) × List (List (List ℤ)) =>
            evalEquationParityFactorJet J ℓ k' dDen
              (evalAffineInputZJetTable J node eqPair.2 indU xList) eqPair.1) ∘
          fun f : ℕ => (eqs'.getD f [], eqRowTables.getD f [])) ∘ Fin.val)
        ((List.finRange eqs'.length).filter p_pred) =
        ((List.finRange eqs'.length).filter p_pred).map F_jet := by
      refine List.map_congr_left fun f _ => ?_
      simp only [Function.comp_apply, List.getD_eq_getElem eqs' [] f.2]
      have hert : eqRowTables.getD f.1 [] =
          (List.range n').map fun v => data.lookupReplacementRow f.1 v := by
        dsimp only [eqRowTables, buildEqRowTables]; exact getD_map_range _ [] f.2
      have hrows_len : ∀ r_tbl ∈ eqRowTables.getD f.1 [], r_tbl.length ≤ n' := by
        rw [hert]; intro r_tbl hr_tbl
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr_tbl
        rw [hdata]; exact length_lookupReplacementRow_le _ _ _ _ _
      rw [toJetTable_evalEquationParityFactorJet_eq dDen node hrows_len indU xList
        (hcan _ (List.getElem_mem f.2)) (hk_deg _ (List.getElem_mem f.2))
        (hvars _ (List.getElem_mem f.2)), hy_U_eq]
      dsimp only [F_jet]; congr 1
      unfold formalEqParityFactor formalClearedMonomialSum
      congr 1; refine Finset.sum_congr rfl fun M hM => ?_
      congr 1; refine Finset.prod_congr rfl fun v hvM => ?_
      have hv_sc : v ∈ scope (emb f) := (hscope_eq f).symm ▸ Finset.mem_biUnion.mpr ⟨M, hM, hvM⟩
      have hrow_eq : (fun i : Fin n' =>
          Polynomial.ofCoeffList (((eqRowTables.getD f.1 []).getD v.1 []).getD i.1 [])) =
          designRows f v := by
        funext i
        rw [hert, getD_map_range _ [] v.2]
        have hf_eq := href.2.2.2.2.1 ⟨emb f, ⟨v, hv_sc⟩⟩
        have hsc_fv : (BalancedSchedules.scopeFactorOf scope ⟨emb f, ⟨v, hv_sc⟩⟩).1 = f.1 ∧
            (BalancedSchedules.scopeVarOf scope ⟨emb f, ⟨v, hv_sc⟩⟩).1 = v.1 :=
          ⟨hemb_val f, rfl⟩
        rw [← hsc_fv.1, ← hsc_fv.2, hf_eq.2.2 i]
        simp only [designRows, hv_sc, ↓reduceDIte]; rfl
      dsimp only; rw [hrow_eq]
    change (List.map _ ((List.finRange eqs'.length).filter p_pred)).prod = _
    rw [hmap_eq, ← List.prod_toFinset F_jet ((List.nodup_finRange _).filter p_pred),
      ← map_prod]
    have hfil_set : ((List.finRange eqs'.length).filter p_pred).toFinset =
        univ.filter (fun f : Fin eqs'.length => D.factorAssign (emb f) t = g) := by
      ext f
      simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, Finset.mem_filter,
        Finset.mem_univ, p_pred, decide_eq_true_eq]
      rw [← hemb_val f, href.2.2.2.1 (emb f) t, Fin.ext_iff]
    rw [hfil_set]
  let term : (∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) → JetTable J ℓ ℤ := fun u =>
    evalJetHom n' J ℓ y_U
      (∏ f : Fin eqs'.length, formalEqParityFactor dDen k' ℓ (designRows f) node
        (localBitsEquiv hVG u) (P_eq f))
  let inFiber : List ℤ → (∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length) → Prop :=
    fun word u => (∀ i ∈ supportOfList n' indE, localBitsEquiv hVG u i = true) ∧
      ∀ g : Fin r, BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 []) (List.ofFn (u g)) =
        (word.drop (g.1 * m_rows)).take m_rows
  have hstep : ∀ (p_par : ℕ × ℕ) (word : List ℤ) (acc : JetRows),
      (measurementStepBody ((p_par, word), (measCtx, acc))).1 = measCtx ∧
      CommonCountingAccum.toJetTable J ℓ
        (measurementStepBody ((p_par, word), (measCtx, acc))).2 =
      CommonCountingAccum.toJetTable J ℓ acc +
        ∑ u ∈ univ.filter (inFiber word), term u := by
    intro p_par word acc
    unfold measurementStepBody
    dsimp only [measCtx]
    split_ifs with hAll
    · refine ⟨rfl, ?_⟩
      rw [CommonCountingAccum.toJetTable_addJet]
      congr 1
      let repOpts : List (Option (List Bool)) := (List.range r).map fun g =>
        BooleanMeasurements.search Prod.fst Prod.snd
          ((grpMeas_t.getD g [], (word.drop (g * m_rows)).take m_rows),
            min (2 * n') (vGroups_t.getD g []).length)
      have hAll_mem : ∀ g : Fin r, (BooleanMeasurements.search Prod.fst Prod.snd
          ((grpMeas_t.getD g.1 [], (word.drop (g.1 * m_rows)).take m_rows),
            (vGroups_t.getD g.1 []).length)).isSome = true := fun g => by
        have hm := (List.all_eq_true.mp hAll) _ (List.mem_map_of_mem (List.mem_range.mpr g.2))
        simpa only [vGroups_t, grpMeas_t, hdg_eq g] using hm
      let reps := repOpts.map fun o => o.getD []
      have hreps_spec : ∀ g : Fin r, (reps.getD g.1 []).length = (vGroups_t.getD g.1 []).length ∧
          BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 []) (reps.getD g.1 []) =
            (word.drop (g.1 * m_rows)).take m_rows := fun g => by
        dsimp only [reps, repOpts]
        rw [List.map_map, getD_map_range _ [] g.2, Function.comp_apply, hdg_eq g]
        obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp (hAll_mem g)
        rw [hys, Option.getD_some]
        exact BooleanMeasurements.search_some Prod.fst Prod.snd _ hys
      let rep : ∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length := fun g j =>
        (reps.getD g.1 [])[j]'(by rw [(hreps_spec g).1]; exact j.2)
      have hreps_ofFn : ∀ g : Fin r, reps.getD g.1 [] = List.ofFn (rep g) := fun g =>
        List.ext_getElem ((hreps_spec g).1.trans (List.length_ofFn).symm) fun k _ _ => by
          simp only [List.getElem_ofFn, rep, Fin.getElem_fin]
      have hrep_meas : ∀ g : Fin r, BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 [])
          (List.ofFn (rep g)) = (word.drop (g.1 * m_rows)).take m_rows := fun g => by
        rw [← hreps_ofFn g]; exact (hreps_spec g).2
      let xStar := buildBaseAssignment n' r vGroups_t reps
      have hgj_ofFn : (List.map (fun g =>
          CommonCountingAccum.streamGroupJetSum evalGroupFactorJet J ℓ
            (min (2 * n') ((data.varGroups.getD t.1 []).getD g []).length)
            ((n', J, ℓ, k'), (node, dDen),
              ((data.varGroups.getD t.1 []).getD g [],
                (data.groupMeasurementMatrices.getD t.1 []).getD g [],
                (word.drop (g * m_rows)).take m_rows),
              (indE, indU, xStar), grpEqLists.getD g [])) (List.range r)) =
          List.ofFn (fun g : Fin r =>
            CommonCountingAccum.streamGroupJetSum evalGroupFactorJet J ℓ
              (vGroups_t.getD g.1 []).length
              ((n', J, ℓ, k'), (node, dDen),
                (vGroups_t.getD g.1 [], grpMeas_t.getD g.1 [],
                  (word.drop (g.1 * m_rows)).take m_rows),
                (indE, indU, xStar), grpEqLists.getD g.1 [])) := by
        refine List.ext_getElem
            (by simp only [List.length_map, List.length_range, List.length_ofFn])
          fun k _ hk => ?_
        have hk_lt : k < r := by simpa only [List.length_ofFn] using hk
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, vGroups_t, grpMeas_t,
          hdg_eq ⟨k, hk_lt⟩]
      change CommonCountingAccum.toJetTable J ℓ (CommonCountingAccum.prodJet J ℓ _) = _
      rw [hgj_ofFn, CommonCountingAccum.toJetTable_prodJet, List.map_ofFn, List.prod_ofFn]
      simp only [Function.comp_apply, CommonCountingAccum.toJetTable_streamGroupJetSum_eq_sum]
      rw [Fintype.prod_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hfib_u : inFiber word u
      · rw [ite_eq_left hfib_u]
        have hg_each : ∀ g : Fin r,
            CommonCountingAccum.toJetTable J ℓ
              (evalGroupFactorJet
                (((n', J, ℓ, k'), (node, dDen),
                  (vGroups_t.getD g.1 [], grpMeas_t.getD g.1 [],
                    (word.drop (g.1 * m_rows)).take m_rows),
                  (indE, indU, xStar), grpEqLists.getD g.1 []),
                ((vGroups_t.getD g.1 []).length, List.ofFn (u g)))) =
            evalJetHom n' J ℓ y_U
              (∏ f ∈ univ.filter (fun f : Fin eqs'.length => D.factorAssign (emb f) t = g),
                formalEqParityFactor dDen k' ℓ (designRows f) node (localBitsEquiv hVG u)
                  (P_eq f)) := by
          intro g
          unfold evalGroupFactorJet; dsimp only
          have hchk_g : checkRestrictedGroup n' indE (vGroups_t.getD g.1 []) (List.ofFn (u g)) =
              true := by
            rw [checkRestrictedGroup_ofFn_iff indE (hVG g).2.1]
            intro j hj
            let v := (groupIdxEquiv hVG g j).1
            have hv_eq : (⟨(vGroups_t.getD g.1 [])[j], (hVG g).2.1 _ (List.getElem_mem j.2)⟩ :
                Fin n') = v := rfl
            have h1 := hfib_u.1 v (hv_eq ▸ hj)
            rwa [localBitsEquiv_apply_of_eq hVG u (groupIdxEquiv hVG g j).2,
              (groupIdxEquiv hVG g).symm_apply_apply j] at h1
          have hdec_g : decide (BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 [])
              (List.ofFn (u g)) = (word.drop (g.1 * m_rows)).take m_rows) = true :=
            decide_eq_true (hfib_u.2 g)
          simp only [hchk_g, hdec_g, Bool.and_self, ↓reduceIte]
          rw [hgrp_prod g]
          have hx_upd : (fun i : Fin n' =>
              (applyGroupBits n' (vGroups_t.getD g.1 []) (List.ofFn (u g)) xStar).getD i.1 false) =
              localBitsEquiv hVG (Function.update rep g (u g)) :=
            funext (getD_applyGroupBits_buildBaseAssignment hVG rep hreps_ofFn g (u g))
          rw [hx_upd]
          refine congrArg (evalJetHom n' J ℓ y_U) (Finset.prod_congr rfl fun f hf => ?_)
          exact formalEqParityFactor_congr_fiber (k' := k') (ℓ := ℓ) hdata href t hVG
            (emb f) (Finset.mem_filter.mp hf).2 (hscope_eq f).symm.subset dDen rep u fun h =>
              (hrep_meas h).trans (hfib_u.2 h).symm
        simp only [hg_each, ← map_prod]
        exact congrArg (evalJetHom n' J ℓ y_U)
          (Finset.prod_fiberwise_of_maps_to (fun f _ => Finset.mem_univ _) _)
      · rw [ite_eq_right hfib_u]
        have hex_zero : ∃ g : Fin r,
            CommonCountingAccum.toJetTable J ℓ
              (evalGroupFactorJet
                (((n', J, ℓ, k'), (node, dDen),
                  (vGroups_t.getD g.1 [], grpMeas_t.getD g.1 [],
                    (word.drop (g.1 * m_rows)).take m_rows),
                  (indE, indU, xStar), grpEqLists.getD g.1 []),
                ((vGroups_t.getD g.1 []).length, List.ofFn (u g)))) = 0 := by
          by_cases hE : ∀ i ∈ supportOfList n' indE, localBitsEquiv hVG u i = true
          · have hnot_m : ¬ ∀ g : Fin r, BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 [])
                (List.ofFn (u g)) = (word.drop (g.1 * m_rows)).take m_rows := fun hm =>
              hfib_u ⟨hE, hm⟩
            push Not at hnot_m
            obtain ⟨g, hg_ne⟩ := hnot_m
            refine ⟨g, ?_⟩
            unfold evalGroupFactorJet; dsimp only
            simp only [decide_eq_false hg_ne, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
              CommonCountingAccum.toJetTable_zeroJet]
          · push Not at hE
            obtain ⟨i, hiE, hi_ne⟩ := hE
            let g := D.varAssign i t
            let j := (groupIdxEquiv hVG g).symm ⟨i, rfl⟩
            refine ⟨g, ?_⟩
            unfold evalGroupFactorJet; dsimp only
            have hchk_f : checkRestrictedGroup n' indE (vGroups_t.getD g.1 []) (List.ofFn (u g)) =
                false := by
              apply Bool.eq_false_iff.mpr; intro hchk_t
              rw [checkRestrictedGroup_ofFn_iff indE (hVG g).2.1] at hchk_t
              have hv_eq : (⟨(vGroups_t.getD g.1 [])[j], (hVG g).2.1 _ (List.getElem_mem j.2)⟩ :
                  Fin n') = i :=
                congrArg Subtype.val ((groupIdxEquiv hVG g).apply_symm_apply ⟨i, rfl⟩)
              have huj : u g j = true := hchk_t j (hv_eq.symm ▸ hiE)
              apply hi_ne
              rw [localBitsEquiv_apply hVG u i]; exact huj
            simp only [hchk_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              CommonCountingAccum.toJetTable_zeroJet]
        obtain ⟨g, hg0⟩ := hex_zero
        exact Finset.prod_eq_zero (Finset.mem_univ g) hg0
    · refine ⟨rfl, ?_⟩
      have hemp : univ.filter (inFiber word) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro u _ hfib_u
        apply hAll
        rw [List.all_eq_true]
        intro opt hopt
        obtain ⟨g_nat, hg_mem, rfl⟩ := List.mem_map.mp hopt
        let g : Fin r := ⟨g_nat, List.mem_range.mp hg_mem⟩
        change (BooleanMeasurements.search Prod.fst Prod.snd
          ((grpMeas_t.getD g.1 [], (word.drop (g.1 * m_rows)).take m_rows),
            min (2 * n') (vGroups_t.getD g.1 []).length)).isSome = true
        rw [hdg_eq g]
        by_contra hns
        have hnone : BooleanMeasurements.search Prod.fst Prod.snd
            ((grpMeas_t.getD g.1 [], (word.drop (g.1 * m_rows)).take m_rows),
              (vGroups_t.getD g.1 []).length) = none :=
          Option.eq_none_iff_forall_not_mem.mpr fun a ha =>
            hns (by rw [Option.mem_def.mp ha]; rfl)
        exact (BooleanMeasurements.search_eq_none_iff_cube Prod.fst Prod.snd _).mp hnone (u g)
          (hfib_u.2 g)
      rw [hemp, Finset.sum_empty, add_zero]
  rw [MeasurementFold.run_accumulator]
  let c_meas := r * m_rows
  let D_cap := r ^ (2 * Q)
  let N_cnt := MeasurementFold.count (c_meas, D_cap)
  have hfold : ∀ (ws : List (List ℤ)) (acc : JetRows),
      (ws.foldl (fun st w => measurementStepBody (((c_meas, D_cap), w), st)) (measCtx, acc)).1 =
        measCtx ∧
      CommonCountingAccum.toJetTable J ℓ
        (ws.foldl (fun st w => measurementStepBody (((c_meas, D_cap), w), st)) (measCtx, acc)).2 =
        CommonCountingAccum.toJetTable J ℓ acc +
          (ws.map fun w => ∑ u ∈ univ.filter (inFiber w), term u).sum := by
    intro ws
    induction ws with
    | nil => intro acc; simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero, and_self]
    | cons w ws ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      have h1 := hstep (c_meas, D_cap) w acc
      have hst : measurementStepBody (((c_meas, D_cap), w), (measCtx, acc)) =
          (measCtx, (measurementStepBody (((c_meas, D_cap), w), (measCtx, acc))).2) :=
        Prod.ext h1.1 rfl
      rw [hst]
      obtain ⟨ih1, ih2⟩ := ih _
      exact ⟨ih1, by rw [ih2, h1.2, add_assoc]⟩
  rw [(hfold _ (zeroJet J ℓ)).2, CommonCountingAccum.toJetTable_zeroJet, zero_add, List.map_map]
  have hrange_ofFn : List.map
      ((fun w => ∑ u ∈ univ.filter (inFiber w), term u) ∘
        Cslib.Radix.measurementValues c_meas D_cap) (List.range N_cnt) =
      List.ofFn (fun idx : Fin N_cnt =>
        ∑ u ∈ univ.filter (inFiber (Cslib.Radix.measurementValues c_meas D_cap idx.1)),
          term u) := by
    refine List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_ofFn])
      fun k _ hk => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Function.comp_apply]
  rw [hrange_ofFn, List.sum_ofFn]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  have hu_collapse : ∀ u : (∀ g : Fin r, BitString (vGroups_t.getD g.1 []).length),
      (∑ idx : Fin N_cnt,
        if inFiber (Cslib.Radix.measurementValues c_meas D_cap idx.1) u then term u else 0) =
      if ∀ i ∈ supportOfList n' indE, localBitsEquiv hVG u i = true then term u else 0 := by
    intro u
    by_cases hEu : ∀ i ∈ supportOfList n' indE, localBitsEquiv hVG u i = true
    · rw [ite_eq_left hEu]
      let L_u : Fin r → List ℤ := fun g =>
        BooleanMeasurements.evalBoolMatrix (grpMeas_t.getD g.1 []) (List.ofFn (u g))
      have hLu_len : ∀ g : Fin r, (L_u g).length = m_rows := fun g => by
        dsimp only [L_u]; rw [BooleanMeasurements.length_evalBoolMatrix, (hgms g).2.1]
      let W : List ℤ := (List.ofFn L_u).flatten
      have hW_len : W.length = c_meas := by
        dsimp only [W, c_meas]
        have hmap_l : List.map List.length (List.ofFn L_u) = List.replicate r m_rows := by
          refine List.ext_getElem (by simp only [List.length_map, List.length_ofFn,
            List.length_replicate]) fun k _ hk => ?_
          have hk_lt : k < r := by simpa only [List.length_replicate] using hk
          simp only [List.getElem_map, List.getElem_ofFn, List.getElem_replicate,
            hLu_len ⟨k, hk_lt⟩]
        rw [List.length_flatten, hmap_l, List.sum_replicate, smul_eq_mul]
      have hW_bnd : ∀ z ∈ W, -(D_cap : ℤ) ≤ z ∧ z ≤ (D_cap : ℤ) := by
        intro z hz
        obtain ⟨sub, hsub, hz_sub⟩ := List.mem_flatten.mp hz
        obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hsub
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hz_sub
        have habs : (BooleanMeasurements.evalBoolRow row (List.ofFn (u g))).natAbs ≤ D_cap :=
          (natAbs_evalBoolRow_le_sum row _).trans ((hgms g).2.2 row hrow).2
        have hcast :
            |(BooleanMeasurements.evalBoolRow row (List.ofFn (u g)) : ℤ)| ≤ (D_cap : ℤ) := by
          rw [← Int.natCast_natAbs]; exact Int.ofNat_le.mpr habs
        exact abs_le.mp hcast
      obtain ⟨idx₀, hidx₀_eq, hidx₀_uniq⟩ :=
        Cslib.Radix.measurementValues_coverage c_meas D_cap W hW_len hW_bnd
      let idx₀' : Fin N_cnt := ⟨idx₀.1, idx₀.2⟩
      rw [Finset.sum_eq_single idx₀']
      · have hf₀ : inFiber (Cslib.Radix.measurementValues c_meas D_cap idx₀'.1) u :=
          ⟨hEu, fun g => ((sliceBlocks_iff_eq_flatten L_u hLu_len
            (Cslib.Radix.length_measurementValues c_meas D_cap idx₀'.1)).mpr hidx₀_eq g).symm⟩
        exact ite_eq_left hf₀
      · intro idx _ hne
        have hnf : ¬ inFiber (Cslib.Radix.measurementValues c_meas D_cap idx.1) u := fun hf =>
          hne (Fin.ext (congrArg Fin.val (hidx₀_uniq ⟨idx.1, idx.2⟩
            ((sliceBlocks_iff_eq_flatten L_u hLu_len
              (Cslib.Radix.length_measurementValues c_meas D_cap idx.1)).mp
              fun g => (hf.2 g).symm))))
        exact ite_eq_right hnf
      · intro hmem; exact (hmem (Finset.mem_univ idx₀')).elim
    · rw [ite_eq_right hEu]
      refine Finset.sum_eq_zero fun idx _ => ?_
      have hnf : ¬ inFiber (Cslib.Radix.measurementValues c_meas D_cap idx.1) u :=
        fun hf => hEu hf.1
      exact ite_eq_right hnf
  simp only [hu_collapse]
  exact Equiv.sum_comp (localBitsEquiv hVG) fun x =>
    if ∀ i ∈ supportOfList n' indE, x i = true then
      evalJetHom n' J ℓ y_U
        (∏ f : Fin eqs'.length, formalEqParityFactor dDen k' ℓ (designRows f) node x (P_eq f))
    else 0

/-! ### 4. Restricted Subset-Pair Möbius Fold and Exact Node Taylor-Jet Identity -/

private theorem jetTable_sum_apply {ι : Type*} {J ℓ : ℕ} (s : Finset ι)
    (f : ι → JetTable J ℓ ℤ) (j : Fin J) (u : Fin ℓ) :
    (∑ a ∈ s, f a) j u = ∑ a ∈ s, f a j u := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact congrArg (f a j u + ·) ih

private theorem jetTable_neg_one_pow_mul_apply {J ℓ : ℕ} (m : ℕ) (T : JetTable J ℓ ℤ)
    (j : Fin J) (u : Fin ℓ) :
    ((-1 : JetTable J ℓ ℤ) ^ m * T) j u = (-1 : ℤ) ^ m * T j u := by
  have hcast : (-1 : JetTable J ℓ ℤ) ^ m = (((-1 : ℤ) ^ m : ℤ) : JetTable J ℓ ℤ) := by
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [hcast, ← zsmul_eq_mul]
  change (((-1 : ℤ) ^ m) • T) j u = (-1 : ℤ) ^ m * T j u
  simp only [JetTable.coe_zsmul, smul_eq_mul]

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
    let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
    let emb : Fin eqs'.length → Fin augScopes.length := fun f =>
      withNeutralScopesIndexEquiv (eqs'.map equationVars) n'
        (Sum.inl ⟨f.1, by simp only [List.length_map]; exact f.2⟩)
    let P_eq : Fin eqs'.length → Finset (Finset (Fin n')) := fun f =>
      HeavyBranchFold.toFinsetEquation n' eqs'[f]
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
          (designReplacementScaledIntMap D emb)) := by
  intro augScopes emb P_eq J m_rows node dDen eqRowTables grpEqLists subCtx
  let scope := listScopeFamily n' augScopes
  let designRows : Fin eqs'.length → Fin n' → Fin n' → Polynomial ℤ := fun f v i =>
    if hv : v ∈ scope (emb f) then
      varReplacementRowScaledInt Q r A₀ R D.place (BalancedSchedules.scopeVarOf scope)
        ⟨emb f, ⟨v, hv⟩⟩ i
    else 0
  let G : Finset (Fin n') → Finset (Fin n') → JetTable J ℓ ℤ := fun E U =>
    ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ E, x i = true),
      evalJetHom n' J ℓ (fun i => bitVal ℤ (decide (i ∈ U)))
        (∏ f : Fin eqs'.length, formalEqParityFactor dDen k' ℓ (designRows f) node x (P_eq f))
  let mobBody : SubsetPairFold.DecodedPair × JetTable J ℓ ℤ → JetTable J ℓ ℤ := fun p =>
    let term := G (supportOfList n' p.1.1) (supportOfList n' p.1.2.1)
    if p.1.2.2 = true then p.2 - term else p.2 + term
  have hsub_fold : ∀ (items : List SubsetPairFold.DecodedPair) (acc : JetRows),
      (items.foldl (fun st item => subsetPairStepBody (item, st)) (subCtx, acc)).1 = subCtx ∧
      CommonCountingAccum.toJetTable J ℓ
        (items.foldl (fun st item => subsetPairStepBody (item, st)) (subCtx, acc)).2 =
      items.foldl (fun accT item => mobBody (item, accT))
        (CommonCountingAccum.toJetTable J ℓ acc) := by
    intro items
    induction items with
    | nil => intro acc; exact ⟨rfl, rfl⟩
    | cons item items ih =>
      intro acc
      simp only [List.foldl_cons]
      have h1_fst : (subsetPairStepBody (item, (subCtx, acc))).1 = subCtx := rfl
      have h1_snd : CommonCountingAccum.toJetTable J ℓ
          (subsetPairStepBody (item, (subCtx, acc))).2 =
          mobBody (item, CommonCountingAccum.toJetTable J ℓ acc) := by
        unfold subsetPairStepBody
        dsimp only [subCtx, mobBody]
        rw [CommonCountingAccum.toJetTable_addJet]
        have hm : CommonCountingAccum.toJetTable J ℓ
            (MeasurementFold.run measurementStepBody (r * m_rows, r ^ (2 * Q))
              (((n', r, m_rows), (J, ℓ, k'), (node, dDen),
                (data.varGroups.getD t.1 [], data.groupMeasurementMatrices.getD t.1 []),
                (item.1, item.2.1), grpEqLists), zeroJet J ℓ)).2.2.2 =
            G (supportOfList n' item.1) (supportOfList n' item.2.1) :=
          toJetTable_measurementFold_eq (J := J) (ℓ := ℓ) hr1 hcan hvars hk_deg hdata href t
            item.1 item.2.1
        cases item.2.2
        · simp only [Bool.false_eq_true, ↓reduceIte, hm]
        · simp only [↓reduceIte, CommonCountingAccum.toJetTable_smulJet, hm, neg_one_smul,
            sub_eq_add_neg]
      have hst : subsetPairStepBody (item, (subCtx, acc)) =
          (subCtx, (subsetPairStepBody (item, (subCtx, acc))).2) := Prod.ext h1_fst rfl
      rw [hst]
      obtain ⟨ih1, ih2⟩ := ih _
      exact ⟨ih1, by rw [ih2, h1_snd]⟩
  have hrun_eq : CommonCountingAccum.toJetTable J ℓ
      (SubsetPairFold.run subsetPairStepBody n' q (subCtx, zeroJet J ℓ)).2 =
      ∑ E ∈ (univ : Finset (Fin n')).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : JetTable J ℓ ℤ) ^ (#E - #U) * G E U := by
    rw [SubsetPairFold.run_eq_foldl_map, (hsub_fold _ (zeroJet J ℓ)).2,
      CommonCountingAccum.toJetTable_zeroJet, ← SubsetPairFold.run_eq_foldl_map mobBody n' q 0,
      SubsetPairFold.run_mobius_eq_sum_restricted_subsets]
  rw [hrun_eq]
  apply JetTable.ext; intro j u_col
  let p_formal : (Fin n' → Bool) → MvPolynomial (Fin n') ℤ := fun x =>
    (((∏ f : Fin eqs'.length, formalEqParityFactor dDen k' ℓ (designRows f) node x
      (P_eq f)).coeff u_col.1).coeff j.1)
  have hG_entry : ∀ E U : Finset (Fin n'),
      G E U j u_col = ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ E, x i = true),
        MvPolynomial.eval (fun i => bitVal ℤ (decide (i ∈ U))) (p_formal x) := fun E U => by
    dsimp only [G]
    rw [jetTable_sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [evalJetHom, RingHom.comp_apply, JetTable.ofPolyVPolyZ_apply,
      Polynomial.coe_mapRingHom, Polynomial.coeff_map, p_formal]
  have hlhs_entry :
      (∑ E ∈ (univ : Finset (Fin n')).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : JetTable J ℓ ℤ) ^ (#E - #U) * G E U) j u_col =
      ∑ E ∈ (univ : Finset (Fin n')).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : ℤ) ^ (#E - #U) *
          ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ E, x i = true),
            MvPolynomial.eval (fun i => bitVal ℤ (decide (i ∈ U))) (p_formal x) := by
    rw [jetTable_sum_apply]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [jetTable_sum_apply]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [jetTable_neg_one_pow_mul_apply, hG_entry]
  have hp_deg : ∀ x : Fin n' → Bool, (p_formal x).totalDegree ≤ q := fun x =>
    (totalDegree_coeff_prod_formalEqParityFactor_le univ dDen k' ℓ designRows node x P_eq
      u_col.1 j.1).trans (Nat.lt_succ_iff.mp j.2)
  have hrhs_entry :
      CommonCountingAccum.taylorOuterVJet J ℓ node
        (univariateClearedParityProduct univ P_eq dDen k' ℓ
          (designReplacementScaledIntMap D emb)) j u_col =
      (Polynomial.taylor node
        ((univariateClearedParityProduct univ P_eq dDen k' ℓ
          (designReplacementScaledIntMap D emb)).coeff u_col.1)).coeff j.1 := rfl
  have hmob_eq :
      (∑ E ∈ (univ : Finset (Fin n')).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : ℤ) ^ (#E - #U) *
          ∑ x ∈ univ.filter (fun x : Fin n' → Bool => ∀ i ∈ E, x i = true),
            MvPolynomial.eval (fun i => bitVal ℤ (decide (i ∈ U))) (p_formal x)) =
      ∑ x : Fin n' → Bool, MvPolynomial.eval (fun i => bitVal ℤ (x i)) (p_formal x) := by
    symm
    convert Cslib.BitString.sum_eval_eq_restricted_subsets q p_formal hp_deg
  rw [hlhs_entry, hrhs_entry, hmob_eq]
  have hscope_eq : ∀ f : Fin eqs'.length, scope (emb f) = equationScope (P_eq f) := fun f => by
    dsimp only [scope, emb, P_eq]
    rw [listScopeFamily_withNeutralScopesList]
    exact listScopeFamily_map_equationVars n' eqs' f
  have hx_term : ∀ x : Fin n' → Bool,
      MvPolynomial.eval (fun i => bitVal ℤ (x i)) (p_formal x) =
      ((∏ f : Fin eqs'.length, parityFactorCleared ℓ (Polynomial.C (dDen ^ k'))
        (clearedMonomialSumPoly dDen k'
          (fun v => Polynomial.taylor node (designReplacementScaledIntMap D emb x f v))
          (P_eq f))).coeff u_col.1).coeff j.1 := fun x => by
    dsimp only [p_formal]
    rw [← Polynomial.coeff_map, ← Polynomial.coe_mapRingHom, ← Polynomial.coeff_map,
      Polynomial.map_prod]
    refine congrArg (fun P : Polynomial (Polynomial ℤ) => (P.coeff u_col.1).coeff j.1)
      (Finset.prod_congr rfl fun f _ => ?_)
    simp only [Polynomial.coe_mapRingHom, formalEqParityFactor,
      map_parityFactorCleared (Polynomial.mapRingHom (MvPolynomial.eval fun i => bitVal ℤ (x i))),
      Polynomial.map_C, MvPolynomial.eval_C]
    congr 1
    rw [formalClearedMonomialSum, Polynomial.map_sum, clearedMonomialSumPoly]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.eval_C, Polynomial.map_prod,
      clearedMonomialPoly]
    congr 1
    refine Finset.prod_congr rfl fun v hvM => ?_
    have hv_sc : v ∈ scope (emb f) := (hscope_eq f).symm ▸ Finset.mem_biUnion.mpr ⟨M, hM, hvM⟩
    rw [Cslib.AffineTaylor.map_eval_self_affineInput,
      designReplacementScaledIntMap_of_mem D emb x hv_sc]
    congr 1
    simp only [designRows, hv_sc, ↓reduceDIte, evalVarReplacementRowScaledIntPoly, mul_comm]
    rfl
  simp only [hx_term]
  have hsum_coeff : (∑ x : Fin n' → Bool,
      ((∏ f : Fin eqs'.length, parityFactorCleared ℓ (Polynomial.C (dDen ^ k'))
        (clearedMonomialSumPoly dDen k'
          (fun v => Polynomial.taylor node (designReplacementScaledIntMap D emb x f v))
          (P_eq f))).coeff u_col.1).coeff j.1) =
      (univariateClearedParityCoord univ P_eq dDen k' ℓ
        (fun x f v => Polynomial.taylor node (designReplacementScaledIntMap D emb x f v))
        u_col.1).coeff j.1 := by
    symm
    change Polynomial.lcoeff ℤ j.1
      (Polynomial.lcoeff (Polynomial ℤ) u_col.1 (∑ x : Fin n' → Bool, _)) = _
    rw [map_sum, map_sum]
    rfl
  rw [hsum_coeff, ← taylor_univariateClearedParityCoord]
  rfl

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
  let b := branchMaxFactorIncidence n' eqs'
  let w := branchMaxFactorWidth n' eqs'
  let β := ParameterCheck.chooseBeta (Nat.clog 2 n') b w
  let r := ReplacementParams.numGroups n'
  let Q := ReplacementParams.numNodes n'
  let R := ReplacementParams.rowBound β n'
  let A₀ := ReplacementParams.intervalStart β n'
  let k' := sysMaxDegree eqs'
  have hr2 : 2 ≤ r := hF.two_le_numGroups
  have hr1 : 1 ≤ r := by omega
  have hRQ : R < Q := hF.rowBound_lt_numNodes
  have hQ_pos : 0 < Q := by omega
  have hmaxQ : max 1 (ReplacementParams.numNodes n') = ReplacementParams.numNodes n' :=
    Nat.max_eq_right (by omega)
  let augScopes := withNeutralScopesList (eqs'.map equationVars) n'
  let edges := scopeIncidencesList n' augScopes
  let scheds := BalancedSchedules.constructBalancedSchedules
    n' augScopes.length Q r (b + w) edges
  let data := buildReplacementDesignData n' (r ^ (2 * Q)) Q r A₀ R augScopes scheds.1 scheds.2
  have hshape' : validDesignShape n' r eqs'.length data = true := by
    simpa only [b, w, β, r, Q, R, A₀, augScopes, edges, scheds, data,
      Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
      Nat.min_eq_right hA₀n, Nat.min_eq_right haux] using hshape
  have href' : data.Refines augScopes D := by
    simpa only [b, w, β, r, Q, R, A₀, augScopes, edges, scheds, data,
      Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
      Nat.min_eq_right hA₀n, Nat.min_eq_right haux] using href
  have hrmeas_le' : r * data.measurementMatrix.length ≤ n' := by
    simpa only [b, w, β, r, Q, R, A₀, augScopes, edges, scheds, data,
      Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
      Nat.min_eq_right hA₀n, Nat.min_eq_right haux] using hrmeas_le
  have hc_meas : min (4 * (n' + 1) * (eqs'.length * n' + n' + 1))
      (r * data.measurementMatrix.length) = r * data.measurementMatrix.length :=
    Nat.min_eq_right (hrmeas_le'.trans (by nlinarith [Nat.zero_le (eqs'.length * n')]))
  unfold evalBoundedIncidenceBranch
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  dsimp only [prepareBranchEvalInput, ParameterCheck.computeScheduleParams]
  simp only [Nat.min_eq_right hQn, Nat.min_eq_right hRn, Nat.min_eq_right hrn,
    Nat.min_eq_right hA₀n, Nat.min_eq_right haux, hmaxQ]
  change (if !validDesignShape n' r eqs'.length data then 0 else _) = _
  simp only [hshape', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hc_meas, href'.2.1]
  let ℓ := n' + 1
  let q := (k' * (R - 1)) * (eqs'.length + 2 * n') / Q
  let J := q + 1
  let dDen : ℤ := (commonDenom Q R : ℤ)
  let emb : Fin eqs'.length → Fin augScopes.length := fun f =>
    withNeutralScopesIndexEquiv (eqs'.map equationVars) n'
      (Sum.inl ⟨f.1, by simp only [List.length_map]; exact f.2⟩)
  let P_eq : Fin eqs'.length → Finset (Finset (Fin n')) := fun f =>
    HeavyBranchFold.toFinsetEquation n' eqs'[f]
  have hk_list : ∀ eq ∈ eqs', ∀ m ∈ eq, m.length ≤ k' := fun eq heq m hm =>
    le_foldl_max_of_mem (List.mem_map_of_mem (List.mem_flatten.mpr ⟨eq, heq, hm⟩))
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
  let Ω : ℤ := ((dDen ^ k') ^ (2 * ℓ - 1)) ^ eqs'.length
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
  have hnodes_nodup : nodes.Nodup :=
    List.Nodup.map (fun a b h => by omega) List.nodup_range
  have hlen_nj : nodeJets.length = nodes.length := by
    simp only [nodeJets, nodes, List.length_map, List.length_range]
  have htaylor_cast : ∀ (z : ℤ) (p : Polynomial ℤ),
      Polynomial.taylor (z : ℚ) (p.map (Int.castRingHom ℚ)) =
        (Polynomial.taylor z p).map (Int.castRingHom ℚ) := by
    intro z p; ext k
    have hz : (z : ℚ) = Int.castRingHom ℚ z := rfl
    simp only [Polynomial.taylor_coeff, Polynomial.coeff_map, Polynomial.hasseDeriv_map]
    rw [hz, Polynomial.eval_map_apply]
  have hclear : ∀ i : Fin nodes.length,
      Ω • CommonCountingAccum.taylorOuterVJet J ℓ (nodes[i] : ℚ) P_rat =
        JetTable.castRingHom ℚ
          (CommonCountingAccum.toJetTable J ℓ (nodeJets[i.1]'(hlen_nj.symm ▸ i.isLt))) := by
    intro i
    have hi_Q : i.1 < Q := by simpa only [nodes, List.length_map, List.length_range] using i.2
    let t : Fin Q := ⟨i.1, hi_Q⟩
    have hnj_t : CommonCountingAccum.toJetTable J ℓ (nodeJets[i.1]'(hlen_nj.symm ▸ i.isLt)) =
        CommonCountingAccum.taylorOuterVJet J ℓ ((t.1 : ℤ) + 1) H_tilde := by
      simp only [nodeJets, List.getElem_map, List.getElem_range]
      exact toJetTable_subsetPairFold_eq hr1 hcan hvars hk_list rfl href' t
    rw [hnj_t]
    apply JetTable.ext; intro j u_col
    have hni : (nodes[i] : ℚ) = (((t.1 : ℤ) + 1 : ℤ) : ℚ) := by
      simp only [nodes, Fin.getElem_fin, List.getElem_map, List.getElem_range, t]
    have hP_coeff : P_rat.coeff u_col.1 =
        (H_tilde.coeff u_col.1).map (Int.castRingHom ℚ) * Polynomial.C ((Ω : ℚ)⁻¹) := by
      simp only [P_rat, Polynomial.coeff_mul_C, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    have hΩq_ne : (Ω : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hΩ_ne
    change (Ω • CommonCountingAccum.taylorOuterVJet J ℓ (nodes[i] : ℚ) P_rat) j u_col =
      (JetTable.castRingHom ℚ (CommonCountingAccum.taylorOuterVJet J ℓ ((t.1 : ℤ) + 1) H_tilde))
        j u_col
    simp only [JetTable.coe_zsmul, zsmul_eq_mul, CommonCountingAccum.taylorOuterVJet]
    change (Ω : ℚ) * (Polynomial.taylor (nodes[i] : ℚ) (P_rat.coeff u_col.1)).coeff j.1 =
      (((Polynomial.taylor ((t.1 : ℤ) + 1) (H_tilde.coeff u_col.1)).coeff j.1 : ℤ) : ℚ)
    rw [hni, hP_coeff, ← Polynomial.taylorAlgHom_apply, map_mul,
      Polynomial.taylorAlgHom_apply, Polynomial.taylorAlgHom_apply, Polynomial.taylor_C,
      Polynomial.coeff_mul_C, htaylor_cast, Polynomial.coeff_map, Int.coe_castRingHom,
      mul_comm _ ((Ω : ℚ)⁻¹), ← mul_assoc, mul_inv_cancel₀ hΩq_ne, one_mul]
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
      nlinarith
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
    refine ⟨(∑ u : Fin ℓ, H_zero u) / (2 : ℤ) ^ ℓ, ?_⟩
    have hedm := Int.mul_ediv_add_emod (∑ u : Fin ℓ, H_zero u) ((2 : ℤ) ^ ℓ)
    change _ = _ * _
    linarith [hmod_eq]
  have hrec := CommonCountingAccum.recoverOuterJetSumModPowTwo_eq hnodes_nodup hΩ_ne nodeJets
    hlen_nj P_rat H_zero hclear hdeg hH0 hcount₀ hcount₁ hdvd
  change min (2 ^ n') (CommonCountingAccum.recoverOuterJetSumModPowTwo nodes J ℓ Ω nodeJets).toNat =
    HeavyBranchFold.rootCount n' eqs'
  rw [hrec, Int.toNat_natCast, Nat.min_eq_right hrc_le]

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
