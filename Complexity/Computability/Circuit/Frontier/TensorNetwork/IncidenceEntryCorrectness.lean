/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceSelections
public import Complexity.Foundations.BooleanAnalysis.SparseIncidence
public import Complexity.Foundations.BooleanAnalysis.MobiusInsert
import all Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedRing
import Complexity.Foundations.Data.Polynomial.CoeffList
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.List.GetD

/-!
# Correctness of executable incidence-entry coefficient extraction

Connect the actual modular coefficient lists and signed streaming subset sums to the multilinear
coefficient formula in [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp. 55–56. These are entry
semantics, not a complete sharper sparse-system or general-density counting algorithm.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.rowPolynomial`: the source product on incidence
  indicators, used only as a mathematical specification.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.val_factorCoeffs`: actual factor coefficients
  represent the source parity polynomial in the truncated ring.
* `Cslib.Circuits.Frontier.IncidenceNetwork.val_rowSum`: the actual signed stream extracts the
  subset Möbius coefficient of that product.
* `Cslib.Circuits.Frontier.IncidenceNetwork.val_rowVertex`: constructed rows satisfy that
  specification with no supplied distinctness or correctness premise.
* `Cslib.Circuits.Frontier.IncidenceNetwork.val_colEntry`: columns count unselected bits.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp. 55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open GaloisRingArith Polynomial Cslib.BitString
open scoped BigOperators

private theorem cast_mod_toNat (P : ℕ) (z : ℤ) :
    (((z % (2 : ℤ) ^ P).toNat : ℕ) : ℤ) = z % (2 : ℤ) ^ P :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

/-- Each written parity-factor coefficient is the canonical residue of the source integer
polynomial's coefficient, including negative linear coefficients and x=0. -/
theorem factorCoeffs_coeff_modEq (P ℓ x j : ℕ) (hj : j < ℓ) :
    ((factorCoeffs P ℓ x).getD j 0 : ℤ) ≡
      (parityFactor ℓ (x : ℤ)).coeff j [ZMOD (2 : ℤ) ^ P] := by
  rw [factorCoeffs, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]
  rw [coeff_parityFactor, ite_eq_left hj, getD_parityLinearCoeffs_eq_parityBaseDigit]
  have hmul : ((x * (x - 1) : ℕ) : ℤ) = (x : ℤ) * (x - 1) := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · rw [Nat.cast_mul, Nat.cast_sub hx]
      norm_num
  have hbase : evalInt (x : ℤ) (parityBaseDigit ℓ j) =
      (parityBaseDigit ℓ j).coeff 0 + (parityBaseDigit ℓ j).coeff 1 * x := by
    rw [evalInt_int]
    conv_lhs => rw [parityBaseDigit_eq_C_add_C_mul_X]
    simp
  rw [hbase, evalInt_hPoly]
  have ha := Int.mod_modEq ((parityBaseDigit ℓ j).coeff 0) ((2 : ℤ) ^ P)
  have hb := Int.mod_modEq ((parityBaseDigit ℓ j).coeff 1) ((2 : ℤ) ^ P)
  have he := (ha.add (hb.mul (Int.ModEq.refl (x : ℤ)))).mul
    ((Int.ModEq.refl ((x : ℤ) * (x - 1))).pow j)
  have hp : (x : ℤ) * ((x - 1 : ℕ) : ℤ) = (x : ℤ) * (x - 1) := by
    simpa only [Nat.cast_mul] using hmul
  simp only [Int.natCast_emod, Int.natCast_mul, Int.natCast_add, Int.natCast_pow,
    Nat.cast_ofNat, cast_mod_toNat, hp]
  convert (Int.mod_modEq _ ((2 : ℤ) ^ P)).trans he using 1; ring

/-- The executable parity-factor list represents the source polynomial in the actual truncated
ring, at arbitrary precision and truncation order. -/
theorem val_factorCoeffs (P ℓ x : ℕ) :
    val P (truncFl ℓ) (factorCoeffs P ℓ x) =
      truncRingHom P ℓ (parityFactor ℓ (x : ℤ)) := by
  rw [← truncNatHom_ofCoeffList]
  apply truncRingHom_eq_iff.mpr
  intro j hj
  simpa only [coe_mapRingHom, coeff_map, coeff_ofCoeffList, Nat.coe_castRingHom] using
    factorCoeffs_coeff_modEq P ℓ x j hj

/-- The actual word traversal, with the implemented signs, extracts a subset Möbius coefficient.
Distinct selected incidences are required so that words and subsets correspond
without multiplicity. -/
theorem sum_enumList_chosenBy {M : Type*} [AddCommGroup M]
    (sel : List (ℕ × ℕ)) (hsel : sel.Nodup) (f : Finset (ℕ × ℕ) → M) :
    ((enumList sel.length).map fun w =>
      (-1 : ℤ) ^ (sel.length - w.count true) • f (chosenBy sel w).toFinset).sum =
        subsetMobius f sel.toFinset := by
  induction sel generalizing f with
  | nil => simp [chosenBy, subsetMobius]
  | cons a sel ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hsel
    rw [List.length_cons, enumList_succ, List.map_flatMap, List.flatMap_def,
      List.sum_flatten, List.map_map]
    simp only [Function.comp_def]
    have hp : ((enumList sel.length).map (fun w =>
        ([false :: w, true :: w].map fun v =>
          (-1 : ℤ) ^ (sel.length + 1 - v.count true) •
            f (chosenBy (a :: sel) v).toFinset).sum)) =
        (enumList sel.length).map (fun w =>
          -((-1 : ℤ) ^ (sel.length - w.count true) • f (chosenBy sel w).toFinset) +
            (-1 : ℤ) ^ (sel.length - w.count true) • f (insert a (chosenBy sel w).toFinset)) := by
      apply List.map_congr_left
      intro w hw
      have hc : w.count true ≤ sel.length :=
        (List.count_le_length).trans_eq (length_of_mem_enumList hw)
      have hs : sel.length + 1 - w.count true = (sel.length - w.count true) + 1 := by omega
      simp [chosenBy, hs, pow_succ]
    have hneg : ((enumList sel.length).map fun w =>
        -((-1 : ℤ) ^ (sel.length - w.count true) • f (chosenBy sel w).toFinset)).sum =
          -((enumList sel.length).map fun w =>
            (-1 : ℤ) ^ (sel.length - w.count true) • f (chosenBy sel w).toFinset).sum := by
      rw [List.sum_neg, List.map_map]
      rfl
    rw [hp, List.sum_map_add, hneg, ih hn f, ih hn (fun T => f (insert a T))]
    rw [List.toFinset_cons, subsetMobius_insert f (by simpa using ha)]
    abel

/-- The product of the source parity factors on an indicator assignment to incidence variables.
Its subset Möbius transform is the coefficient of the indicated squarefree monomial. -/
noncomputable def rowPolynomial (ℓ : ℕ) (tests : List (List (List ℕ)))
    (T : Finset (ℕ × ℕ)) : ℤ[X] :=
  ((List.range tests.length).map fun t =>
    parityFactor ℓ (monomialsIn (tests.getD t []) t T.toList : ℤ)).prod

/-- Integer lifts depend only on membership of the chosen incidences. -/
theorem monomialsIn_toFinset (test : List (List ℕ)) (t : ℕ) (sel : List (ℕ × ℕ)) :
    monomialsIn test t sel.toFinset.toList = monomialsIn test t sel := by
  simp [monomialsIn]

/-- Actual modular row products represent the product of parity factors in the truncated ring. -/
theorem val_rowTerm (P ℓ : ℕ) (tests : List (List (List ℕ))) (sel : List (ℕ × ℕ)) :
    val P (truncFl ℓ) (rowTerm P ℓ tests sel) =
      truncRingHom P ℓ (rowPolynomial ℓ tests sel.toFinset) := by
  have hfold (ts : List ℕ) (acc : List ℕ) :
      val P (truncFl ℓ) (ts.foldl (fun acc t =>
        mul P (truncFl ℓ) acc (factorCoeffs P ℓ (monomialsIn (tests.getD t []) t sel))) acc) =
      val P (truncFl ℓ) acc *
        ((ts.map fun t => truncRingHom P ℓ
          (parityFactor ℓ (monomialsIn (tests.getD t []) t sel : ℤ))).prod) := by
    induction ts generalizing acc with
    | nil => simp
    | cons t ts ih =>
      rw [List.foldl_cons, ih, val_mul, val_factorCoeffs]
      simp only [List.map_cons, List.prod_cons]
      ring
  rw [rowTerm, hfold, val_one, one_mul, rowPolynomial, map_list_prod]
  simp only [List.map_map, Function.comp_def, monomialsIn_toFinset]

private theorem val_rowFold (P ℓ : ℕ) (tests : List (List (List ℕ)))
    (sel : List (ℕ × ℕ)) (ws : List (List Bool)) (acc : List ℕ) :
    val P (truncFl ℓ) ((ws.foldl (fun st w => rowBody ((sel.length, w), st))
      ((P, ℓ, tests, sel), acc)).2) = val P (truncFl ℓ) acc +
        (ws.map fun w => (-1 : ℤ) ^ (sel.length - w.count true) •
          val P (truncFl ℓ) (rowTerm P ℓ tests (chosenBy sel w))).sum := by
  induction ws generalizing acc with
  | nil => simp
  | cons w ws ih =>
    rw [List.foldl_cons]
    by_cases he : (sel.length - w.count true) % 2 = 0
    · have hstep : rowBody ((sel.length, w), ((P, ℓ, tests, sel), acc)) =
          ((P, ℓ, tests, sel), add P (truncFl ℓ) acc
            (rowTerm P ℓ tests (chosenBy sel w))) := by simp [rowBody, he]
      rw [hstep, ih, val_add]
      simp [neg_one_pow_eq_ite, Nat.even_iff, he, List.map_cons, List.sum_cons, add_assoc]
    · have hstep : rowBody ((sel.length, w), ((P, ℓ, tests, sel), acc)) =
          ((P, ℓ, tests, sel), sub P (truncFl ℓ) acc
            (rowTerm P ℓ tests (chosenBy sel w))) := by simp [rowBody, he]
      rw [hstep, ih, val_sub]
      simp [neg_one_pow_eq_ite, Nat.even_iff, he, List.map_cons, List.sum_cons, sub_eq_add_neg,
        add_assoc]

/-- The actual signed streaming sum extracts the squarefree incidence coefficient of the source
product, in the actual truncated coefficient ring. This verifies the signs
and modular reductions. -/
theorem val_rowSum (P ℓ : ℕ) (tests : List (List (List ℕ))) (sel : List (ℕ × ℕ))
    (hsel : sel.Nodup) :
    val P (truncFl ℓ) (rowSum (P, ℓ, tests, sel)) =
      truncRingHom P ℓ (subsetMobius (rowPolynomial ℓ tests) sel.toFinset) := by
  rw [rowSum, val_rowFold, val_zero, zero_add]
  simp only [val_rowTerm]
  exact (sum_enumList_chosenBy sel hsel
    (fun T => truncRingHom P ℓ (rowPolynomial ℓ tests T))).trans
      (map_subsetMobius (truncRingHom P ℓ).toAddMonoidHom (rowPolynomial ℓ tests) sel.toFinset).symm

/-- Generic entry correctness for disjoint incidence blocks, including zero at invalid indices. -/
theorem val_rowEntry (P ℓ : ℕ) (tests : List (List (List ℕ))) (blocks : List Block)
    (hblocks : (blocks.flatMap Prod.fst).Nodup) (bs : List Bool) :
    val P (truncFl ℓ) (rowEntry (P, ℓ, tests, blocks) bs) =
      if validIndices blocks (blockIndices blocks bs) then
        truncRingHom P ℓ (subsetMobius (rowPolynomial ℓ tests)
          (selected blocks (blockIndices blocks bs)).toFinset) else 0 := by
  rw [rowEntry]
  split_ifs
  · exact val_rowSum P ℓ tests _ (hblocks.sublist (selected_sublist _ _))
  · simp [val]

/-- The actual constructed row extracts the source multilinear coefficient. Its incidence
selection is proved distinct by construction; no selected-set or entry-correctness
advice is needed. -/
theorem val_rowVertex (P ℓ J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (g : ℕ)
    (bs : List Bool) :
    val P (truncFl ℓ) (incEntry (rowVertex P ℓ J sys d g).2 bs) =
      if validIndices (rowBlocks J sys d g) (blockIndices (rowBlocks J sys d g) bs) then
        truncRingHom P ℓ (subsetMobius
          (rowPolynomial ℓ ((List.residueClass J sys.length g).map (sys.getD · [])))
          (selected (rowBlocks J sys d g) (blockIndices (rowBlocks J sys d g) bs)).toFinset)
      else 0 :=
  val_rowEntry P ℓ _ _ (nodup_rowBlocks J sys d g) bs

/-- The actual column entry leaves exactly the unselected declared variables free, with its
binary power interpreted in the same truncated ring as the row coefficients. -/
theorem val_colEntry (P ℓ : ℕ) (vars : List ℕ) (blocks : List Block) (bs : List Bool) :
    val P (truncFl ℓ) (colEntry (P, vars, blocks) bs) =
      (2 : Ring P (truncFl ℓ)) ^
        unselectedCount vars (selected blocks (blockIndices blocks bs)) := by
  rw [colEntry, ← truncNatHom_ofCoeffList]
  simp [Polynomial.ofCoeffList_cons, truncNatHom, truncRingHom, natCast_mod_two_pow]

end Cslib.Circuits.Frontier.IncidenceNetwork
