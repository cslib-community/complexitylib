/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Runtime.HermiteCramer
public import Complexity.Computability.GenericRAM.Native.BooleanFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.PolyTime.JetArray
public import Complexity.Foundations.Data.Polynomial.StagedJetArithmetic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Foundations.Data.List.Fold
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.GetD

/-!
# Streaming group-sum and outer Taylor-jet accumulators with Cramer recovery

Proposition 3.4 (§3.3–3.5, pp. 22–26), Proposition 5.3 (§5.3–5.4, pp. 37–38), and Appendix B.2–B.3
(pp. 48–50) of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] evaluate
`H_t(z) = H(t + z) mod z^J` over `ℚ[V]/(V^ℓ)[z]/(z^J)` in streaming stages over fixed-denominator
`J × ℓ` integer arrays (`JetRows`), followed by confluent Hermite Cramer recovery.

`toJetTable`, `ofJetTable`, `taylorOuterVJet`, `groupSumBody`, `streamGroupJetSumPrefix`,
`combineOuterRound`, `outerAccumBody`, and `streamOuterJetAccumPrefix` provide unencoded algebraic
and prefix-fold specifications (`JetRows ↔ JetTable J ℓ ℤ`, `R[T][V] →+* JetTable J ℓ R`), whereas
`extractCoordNodeJets`, `extractAllCoordNodeJets`, `prodJet`, `weightedProdJet`, and
`recoverOuterJetSumModPowTwo` carry plain `ComputableInPolyTime` (`@[fun_prop]`) certificates, and
`streamGroupJetSum` / `streamOuterJetAccum` carry uniform `NativeCertificate`, `ComputableInO`, and
plain `ComputableInPolySpace` bounds (never claiming whole-loop `PolyTime`). Out-of-range entry and
node lookups return `0` and `[]`; `ofJetTable` returns `[]` for `J = 0` and `List.replicate J []`
for `ℓ = 0`; `prodJet` returns `constJet J ℓ 1` on `[]`; `weightedProdJet` returns `zeroJet J ℓ`
when `w = 0`; clearing theorems hold in any `CommRing K`; and Cramer recovery requires `Ω ≠ 0` and
`nodes.Nodup`, returning `0` via `Int.ediv` when `Ω = 0`, `ℓ = 0`, or `detRows = 0`.

## Main definitions

* `Cslib.CommonCountingAccum.toJetTable`, `Cslib.CommonCountingAccum.ofJetTable`,
  `Cslib.CommonCountingAccum.taylorOuterVJet`: `JetRows ↔ JetTable J ℓ ℤ` bridge and Taylor-jet
  homomorphism `R[T][V] →+* JetTable J ℓ R`.
* `Cslib.CommonCountingAccum.extractCoordNodeJets`, `Cslib.CommonCountingAccum.prodJet`,
  `Cslib.CommonCountingAccum.weightedProdJet`, `Cslib.CommonCountingAccum.extractAllCoordNodeJets`:
  per-coordinate `Q × J` node-jet slicing, truncated `r`-fold Cauchy product, and scalar weighting.
* `Cslib.CommonCountingAccum.streamGroupJetSum`, `Cslib.CommonCountingAccum.groupJetSumCertificate`,
  `Cslib.CommonCountingAccum.streamOuterJetAccum`,
  `Cslib.CommonCountingAccum.outerJetAccumCertificate`: streaming `2 ^ d` group sum (`BooleanFold`)
  and `T_rounds` outer round accumulator (`IndexFold`) with uniform `NativeCertificate`s.
* `Cslib.CommonCountingAccum.recoverOuterJetSumModPowTwo`: multi-coordinate Hermite Cramer count
  recovery `(∑_{u < ℓ} H_u(0)).modPowTwo ℓ` across `Q` evaluation nodes.

## Main results

* `Cslib.CommonCountingAccum.toJetTable_ofJetTable`,
  `Cslib.CommonCountingAccum.ofJetTable_toJetTable`,
  `Cslib.CommonCountingAccum.length_encJetRows_le_of_l1Norm_le`,
  `Cslib.CommonCountingAccum.rowEntry_extractCoordNodeJets_eq_taylor`,
  `Cslib.CommonCountingAccum.cast_prodJet_ofFn_cleared`,
  `Cslib.CommonCountingAccum.computableInPolyTime_prodJet`: Stage-2 bridge, clearing, & `PolyTime`.
* `Cslib.CommonCountingAccum.cast_streamGroupJetSum_cleared`,
  `Cslib.CommonCountingAccum.toJetTable_prodJet_streamGroupJetSum`,
  `Cslib.CommonCountingAccum.length_encJetRows_streamGroupJetSumPrefix_le`,
  `Cslib.CommonCountingAccum.computableInO_streamGroupJetSum`,
  `Cslib.CommonCountingAccum.computableInPolySpace_streamGroupJetSum`: Stage-3 local group sum.
* `Cslib.CommonCountingAccum.cast_streamOuterJetAccum_taylorOuterVJet`,
  `Cslib.CommonCountingAccum.length_encJetRows_streamOuterJetAccumPrefix_le`,
  `Cslib.CommonCountingAccum.computableInO_outerJetAccumCertificate`,
  `Cslib.CommonCountingAccum.computableInPolySpace_streamOuterJetAccum`: Stage-4 outer accumulation.
* `Cslib.CommonCountingAccum.hermiteRecoverZero_extractCoordNodeJets_eq`,
  `Cslib.CommonCountingAccum.recoverOuterJetSumModPowTwo_eq`,
  `Cslib.CommonCountingAccum.recoverOuterJetSumModPowTwo_streamOuterJetAccum_eq`,
  `Cslib.CommonCountingAccum.computableInPolyTime_recoverOuterJetSumModPowTwo`: Cramer recovery.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §3.3–3.5, §5.3–5.4, B.2–B.3
-/

@[expose] public section

namespace Cslib.CommonCountingAccum

open Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM
open ComputableTidilyInO (length_encNat_mono)

local notation "encJet" => encList (encList encIntBin)
local notation "encJets" => encList (encList (encList encIntBin))
local notation "encDims" => encPair encUnary encUnary
local notation "encAccum" "(" ctx ")" => encPair (encPair encDims ctx) encJet
local notation "encRoundOut" => encPair encIntBin encJets

/-! ### 1. `JetRows` ↔ `JetTable` bridge, `taylorOuterVJet`, node slicing, and `prodJet` -/

/-- Interpret `A : JetRows` as a `(J × ℓ)` `JetTable` via `Cslib.rowEntry` (out-of-range = `0`). -/
def toJetTable (J ℓ : ℕ) (A : JetRows) : JetTable J ℓ ℤ := JetTable.of fun j u => rowEntry A j u

@[simp] theorem toJetTable_apply (J ℓ : ℕ) (A : JetRows) (j : Fin J) (u : Fin ℓ) :
    toJetTable J ℓ A j u = rowEntry A j u := rfl

/-- Tabulate `T : JetTable J ℓ ℤ` into a dense `(J × ℓ)` integer table (`[]` when `J = 0`, and
`List.replicate J []` when `ℓ = 0`). -/
def ofJetTable {J ℓ : ℕ} (T : JetTable J ℓ ℤ) : JetRows :=
  tabulateTable J ℓ fun j u => if h : j < J ∧ u < ℓ then T ⟨j, h.1⟩ ⟨u, h.2⟩ else 0

theorem isTableShape_ofJetTable {J ℓ : ℕ} (T : JetTable J ℓ ℤ) : IsTableShape J ℓ (ofJetTable T) :=
  isTableShape_tabulateTable J ℓ _
@[simp] theorem ofJetTable_zero_rows {ℓ : ℕ} (T : JetTable 0 ℓ ℤ) : ofJetTable T = [] := rfl
@[simp] theorem ofJetTable_zero_cols {J : ℕ} (T : JetTable J 0 ℤ) :
    ofJetTable T = List.replicate J [] := by
  apply List.ext_getElem (by simp only [ofJetTable, tabulateTable, List.length_map,
    List.length_range, List.length_replicate])
  intro _ _ _; simp only [ofJetTable, tabulateTable, List.getElem_map, List.range_zero,
    List.map_nil, List.getElem_replicate]

theorem rowEntry_ofJetTable_of_lt {J ℓ : ℕ} (T : JetTable J ℓ ℤ) {j u : ℕ} (hj : j < J)
    (hu : u < ℓ) : rowEntry (ofJetTable T) j u = T ⟨j, hj⟩ ⟨u, hu⟩ := by
  rw [ofJetTable, rowEntry_tabulateTable_of_lt _ hj hu]; simp only [hj, hu, and_self, ↓reduceDIte]
@[simp] theorem toJetTable_ofJetTable {J ℓ : ℕ} (T : JetTable J ℓ ℤ) :
    toJetTable J ℓ (ofJetTable T) = T :=
  JetTable.ext fun j u => rowEntry_ofJetTable_of_lt T j.isLt u.isLt
theorem ofJetTable_toJetTable {J ℓ : ℕ} {A : JetRows} (hA : IsTableShape J ℓ A) :
    ofJetTable (toJetTable J ℓ A) = A :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_ofJetTable _) hA fun _ hj _ hu =>
    rowEntry_ofJetTable_of_lt _ hj hu
theorem eq_of_isTableShape_of_toJetTable_eq {J ℓ : ℕ} {A B : JetRows} (hA : IsTableShape J ℓ A)
    (hB : IsTableShape J ℓ B) (h : toJetTable J ℓ A = toJetTable J ℓ B) : A = B := by
  rw [← ofJetTable_toJetTable hA, ← ofJetTable_toJetTable hB, h]

@[simp] theorem toJetTable_zeroJet (J ℓ : ℕ) : toJetTable J ℓ (zeroJet J ℓ) = 0 :=
  JetTable.ext fun _ _ => by simp only [toJetTable_apply, rowEntry_zeroJet, JetTable.coe_zero]
theorem toJetTable_constJet (J ℓ : ℕ) (c : ℤ) :
    toJetTable J ℓ (constJet J ℓ c) = JetTable.const c :=
  JetTable.ext fun j u => by
    rw [toJetTable_apply, rowEntry_constJet c j.isLt u.isLt, JetTable.const_apply]
@[simp] theorem toJetTable_constJet_one (J ℓ : ℕ) : toJetTable J ℓ (constJet J ℓ 1) = 1 :=
  toJetTable_constJet J ℓ 1
@[simp] theorem toJetTable_addJet (J ℓ : ℕ) (A B : JetRows) :
    toJetTable J ℓ (addJet J ℓ A B) = toJetTable J ℓ A + toJetTable J ℓ B :=
  JetTable.ext fun j u => by
    simp only [toJetTable_apply, rowEntry_addJet A B j.isLt u.isLt, JetTable.coe_add]
@[simp] theorem toJetTable_smulJet (J ℓ : ℕ) (c : ℤ) (A : JetRows) :
    toJetTable J ℓ (smulJet J ℓ c A) = c • toJetTable J ℓ A :=
  JetTable.ext fun j u => by
    simp only [toJetTable_apply, rowEntry_smulJet c A j.isLt u.isLt, JetTable.coe_zsmul,
      smul_eq_mul]

private theorem sum_fin_filter_eq_range {M : Type*} [AddCommMonoid M] {N : ℕ} (k : Fin N)
    (g : ℕ → ℕ → M) :
    (∑ a : Fin N, ∑ b ∈ Finset.univ.filter (fun b : Fin N => (a : ℕ) + (b : ℕ) = (k : ℕ)),
      g a b) = ∑ a ∈ Finset.range ((k : ℕ) + 1), g a ((k : ℕ) - a) := by
  simp only [Finset.sum_filter]; rw [← Finset.sum_product', ← Finset.sum_filter]
  refine Finset.sum_bij (fun ab _ => (ab.1 : ℕ)) ?_ ?_ ?_ ?_
  · intro ab hab; simp only [Finset.mem_filter] at hab; exact Finset.mem_range.mpr (by omega)
  · intro ab₁ h₁ ab₂ h₂ h; simp only [Finset.mem_filter] at h₁ h₂
    have e₁ := h₁.2; have e₂ := h₂.2; exact Prod.ext (Fin.ext h) (Fin.ext (by omega))
  · intro a ha; have hlt := Finset.mem_range.mp ha; have hk : (k : ℕ) < N := k.2
    refine ⟨(⟨a, by omega⟩, ⟨(k : ℕ) - a, by omega⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]; omega
  · intro ab hab; simp only [Finset.mem_filter] at hab
    have e := hab.2; exact congrArg (g (ab.1 : ℕ)) (by omega)

@[simp] theorem toJetTable_convJet (J ℓ : ℕ) (A B : JetRows) :
    toJetTable J ℓ (convJet J ℓ A B) = toJetTable J ℓ A * toJetTable J ℓ B := by
  ext j u; rw [toJetTable_apply, rowEntry_convJet A B j.isLt u.isLt, JetTable.mul_eq_conv,
    JetTable.conv_apply]
  have hu (j₁ j₂ : Fin J) :=
    sum_fin_filter_eq_range u fun u₁ u₂ => rowEntry A j₁ u₁ * rowEntry B j₂ u₂
  simpa only [toJetTable_apply, hu] using (sum_fin_filter_eq_range j fun j₁ j₂ =>
    ∑ u₁ ∈ Finset.range ((u : ℕ) + 1), rowEntry A j₁ u₁ * rowEntry B j₂ ((u : ℕ) - u₁)).symm

theorem l1Norm_toJetTable_eq {J ℓ : ℕ} {A : JetRows} (hA : IsTableShape J ℓ A) :
    (toJetTable J ℓ A).l1Norm = jetL1Norm A := by
  have h (j : Fin J) := Fin.sum_univ_eq_sum_range (fun u => (rowEntry A j u).natAbs) ℓ
  have hsum : (toJetTable J ℓ A).l1Norm =
      ∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ, (rowEntry A j u).natAbs := by
    simpa only [JetTable.l1Norm, toJetTable_apply, h] using
      Fin.sum_univ_eq_sum_range (fun j => ∑ u ∈ Finset.range ℓ, (rowEntry A j u).natAbs) J
  exact hsum.trans (jetL1Norm_eq_sum_rowEntry hA).symm

/-- Encoded bit-length bound for `(J, ℓ)`-shaped `A` (`hA`) with entry `natAbs.size ≤ b`. -/
theorem length_encJetRows_le_of_size_le {J ℓ b : ℕ} {A : JetRows} (hA : IsTableShape J ℓ A)
    (hb : ∀ j < J, ∀ u < ℓ, (rowEntry A j u).natAbs.size ≤ b) :
    (encJet A).length ≤ J * (2 * (ℓ * (2 * b + 3)) + 1) := by
  have hrow_len : ∀ row ∈ A, (encList encIntBin row).length ≤ ℓ * (2 * b + 3) := fun row hrow => by
    have hrlen : row.length = ℓ := hA.2 row hrow
    have h1 := length_encList_le encIntBin row (b := b + 1) fun z hz => by
      obtain ⟨j, u, hj, hu, rfl⟩ := exists_rowEntry_eq_of_mem hrow hz
      rw [length_encIntBin]; exact Nat.add_le_add_right (hb j (hA.1 ▸ hj) u (hrlen ▸ hu)) 1
    rwa [hrlen, show 2 * (b + 1) + 1 = 2 * b + 3 by omega] at h1
  have hA_len := length_encList_le (encList encIntBin) A hrow_len; rwa [hA.1] at hA_len

theorem length_encJetRows_le_of_natAbs_le {J ℓ M : ℕ} {A : JetRows} (hA : IsTableShape J ℓ A)
    (hM : ∀ j < J, ∀ u < ℓ, (rowEntry A j u).natAbs ≤ M) :
    (encJet A).length ≤ J * (2 * (ℓ * (2 * M.size + 3)) + 1) :=
  length_encJetRows_le_of_size_le hA fun j hj u hu => Nat.size_le_size (hM j hj u hu)
/-- Encoded bit-length bound from `(toJetTable J ℓ A).l1Norm ≤ L` under `IsTableShape J ℓ A`. -/
theorem length_encJetRows_le_of_l1Norm_le {J ℓ L : ℕ} {A : JetRows} (hA : IsTableShape J ℓ A)
    (hL : (toJetTable J ℓ A).l1Norm ≤ L) :
    (encJet A).length ≤ J * (2 * (ℓ * (2 * L.size + 3)) + 1) :=
  length_encJetRows_le_of_natAbs_le hA fun j _ u _ =>
    (natAbs_rowEntry_le_jetL1Norm A j u).trans ((l1Norm_toJetTable_eq hA).symm.trans_le hL)
theorem size_natAbs_le_length_encJetRows {A : JetRows} {row : List ℤ} (hrow : row ∈ A)
    {z : ℤ} (hz : z ∈ row) : z.natAbs.size ≤ (encJet A).length := by
  have h1 : (encIntBin z).length ≤ (encList encIntBin row).length :=
    SizedListEncoding.length_elem_le row z hz
  have h2 : (encList encIntBin row).length ≤ (encJet A).length :=
    SizedListEncoding.length_elem_le A row hrow
  have h := h1.trans h2; rw [length_encIntBin] at h; omega
theorem size_natAbs_rowEntry_le_length_encJetRows (A : JetRows) (j u : ℕ) :
    (rowEntry A j u).natAbs.size ≤ (encJet A).length :=
  rowEntry_rel_of_mem (by simp only [Int.natAbs_zero, Nat.size_zero, Nat.zero_le])
    (fun _ hrow _ hz => size_natAbs_le_length_encJetRows hrow hz) j u

/-- Taylor jet extraction homomorphism `R[T][V] →+* JetTable J ℓ R` at node `t : R`
(outer indeterminate `V`, inner indeterminate `T`). -/
noncomputable def taylorOuterVJet (J ℓ : ℕ) {R : Type*} [CommRing R] (t : R) :
    Polynomial (Polynomial R) →+* JetTable J ℓ R where
  toFun P := JetTable.of fun j u => (Polynomial.taylor t (P.coeff u)).coeff j
  map_one' := JetTable.ext fun j u => by
    simp only [JetTable.of_apply, JetTable.one_eq_const, JetTable.const_apply]
    by_cases hu : (u : ℕ) = 0 <;> by_cases hj : (j : ℕ) = 0 <;>
      simp only [hu, hj, and_self, and_false, false_and, ↓reduceIte, Polynomial.taylor_one,
        Polynomial.C_1, Polynomial.coeff_one, LinearMap.map_zero, Polynomial.coeff_zero]
  map_mul' P Q := JetTable.ext fun j u => by
    change (Polynomial.taylor t ((P * Q).coeff u)).coeff j =
      JetTable.conv (JetTable.of fun j' u' => (Polynomial.taylor t (P.coeff u')).coeff j')
        (JetTable.of fun j' u' => (Polynomial.taylor t (Q.coeff u')).coeff j') j u
    rw [JetTable.conv_apply]; dsimp only [JetTable.of]
    have hmul (u₁ : ℕ) : (Polynomial.taylor t (P.coeff u₁ * Q.coeff ((u : ℕ) - u₁))).coeff j =
        ∑ j₁ ∈ Finset.range ((j : ℕ) + 1), (Polynomial.taylor t (P.coeff u₁)).coeff j₁ *
          (Polynomial.taylor t (Q.coeff ((u : ℕ) - u₁))).coeff ((j : ℕ) - j₁) := by
      rw [show Polynomial.taylor t (P.coeff u₁ * Q.coeff ((u : ℕ) - u₁)) =
        Polynomial.taylor t (P.coeff u₁) * Polynomial.taylor t (Q.coeff ((u : ℕ) - u₁)) by
          simp only [Polynomial.taylor_apply, Polynomial.mul_comp]]
      exact (Polynomial.coeff_mul _ _ j).trans (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun j₁ j₂ => (Polynomial.taylor t (P.coeff u₁)).coeff j₁ *
          (Polynomial.taylor t (Q.coeff ((u : ℕ) - u₁))).coeff j₂) j)
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun u₁ u₂ => P.coeff u₁ * Q.coeff u₂) u, map_sum, Polynomial.finsetSum_coeff]
    simp only [Nat.succ_eq_add_one, hmul]; rw [Finset.sum_comm]
    have hu (j₁ j₂ : Fin J) := sum_fin_filter_eq_range u fun u₁ u₂ =>
      (Polynomial.taylor t (P.coeff u₁)).coeff j₁ * (Polynomial.taylor t (Q.coeff u₂)).coeff j₂
    simpa only [hu] using (sum_fin_filter_eq_range j fun j₁ j₂ =>
      ∑ u₁ ∈ Finset.range ((u : ℕ) + 1), (Polynomial.taylor t (P.coeff u₁)).coeff j₁ *
        (Polynomial.taylor t (Q.coeff ((u : ℕ) - u₁))).coeff j₂).symm
  map_zero' := JetTable.ext fun _ _ => by
    simp only [JetTable.of_apply, Polynomial.coeff_zero, LinearMap.map_zero, JetTable.coe_zero]
  map_add' P Q := JetTable.ext fun _ _ => by
    simp only [JetTable.of_apply, JetTable.coe_add, Polynomial.coeff_add, LinearMap.map_add]

@[simp] theorem taylorOuterVJet_apply (J ℓ : ℕ) {R : Type*} [CommRing R] (t : R)
    (P : Polynomial (Polynomial R)) (j : Fin J) (u : Fin ℓ) :
    taylorOuterVJet J ℓ t P j u = (Polynomial.taylor t (P.coeff u)).coeff j := rfl

/-- Extract the `nodeJets.length × J` Taylor-jet table at `V ^ u` across per-node `J × ℓ` arrays
`nodeJets`, indexed `(nodeIdx, derivOrder)` (out-of-range node/entry lookups default to `[]`/`0`;
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix B.3, p. 50). -/
def extractCoordNodeJets (J u : ℕ) (nodeJets : List JetRows) : JetRows :=
  tabulateTable nodeJets.length J fun i j => rowEntry (nodeJets.getD i []) j u

/-- Extract all `ℓ` per-coordinate `nodeJets.length × J` Taylor-jet tables (`u = 0, …, ℓ - 1`). -/
def extractAllCoordNodeJets (J ℓ : ℕ) (nodeJets : List JetRows) : List JetRows :=
  (List.range ℓ).map fun u => extractCoordNodeJets J u nodeJets

theorem isTableShape_extractCoordNodeJets (J u : ℕ) (nodeJets : List JetRows) :
    IsTableShape nodeJets.length J (extractCoordNodeJets J u nodeJets) :=
  isTableShape_tabulateTable nodeJets.length J _
@[simp] theorem length_extractAllCoordNodeJets (J ℓ : ℕ) (nodeJets : List JetRows) :
    (extractAllCoordNodeJets J ℓ nodeJets).length = ℓ := by
  simp only [extractAllCoordNodeJets, List.length_map, List.length_range]
theorem rowEntry_extractCoordNodeJets_of_lt (J u : ℕ) (nodeJets : List JetRows) {i j : ℕ}
    (hi : i < nodeJets.length) (hj : j < J) :
    rowEntry (extractCoordNodeJets J u nodeJets) i j = rowEntry nodeJets[i] j u := by
  rw [extractCoordNodeJets, rowEntry_tabulateTable_of_lt _ hi hj, List.getD_eq_getElem _ _ hi]

/-- Under `hlen` and `hclear`, `extractCoordNodeJets` gives the `Ω`-scaled `(i, j)` Taylor
coefficients of `P.coeff u` (unconditional in `K`). -/
theorem rowEntry_extractCoordNodeJets_eq_taylor {J ℓ : ℕ} {K : Type*} [CommRing K]
    (Ω : ℤ) (nodes : List ℤ) (nodeJets : List JetRows) (hlen : nodeJets.length = nodes.length)
    (P : Polynomial (Polynomial K))
    (hclear : ∀ i : Fin nodes.length, Ω • taylorOuterVJet J ℓ (nodes[i] : K) P =
      JetTable.castRingHom K (toJetTable J ℓ (nodeJets[i.1]'(hlen.symm ▸ i.isLt))))
    (u : Fin ℓ) (i : Fin nodes.length) (j : Fin J) :
    (rowEntry (extractCoordNodeJets J u nodeJets) i j : K) =
      (Ω : K) * (Polynomial.taylor (nodes[i] : K) (P.coeff u)).coeff j := by
  rw [rowEntry_extractCoordNodeJets_of_lt J u nodeJets (hlen.symm ▸ i.isLt) j.isLt]
  simpa only [JetTable.coe_zsmul, zsmul_eq_mul, taylorOuterVJet_apply, JetTable.castRingHom_apply,
    toJetTable_apply] using (congr_fun (congr_fun (hclear i) j) u).symm

@[fun_prop] theorem computableInPolyTime_extractCoordNodeJets {α : Type} {encIn : α ↪ List Bool}
    {J u : α → ℕ} {nodeJets : α → List JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hu : ComputableInPolyTime u encIn encUnary)
    (hnodeJets : ComputableInPolyTime nodeJets encIn encJets) :
    ComputableInPolyTime (fun x => extractCoordNodeJets (J x) (u x) (nodeJets x)) encIn encJet := by
  have hr : ComputableInPolyTime (fun x => (nodeJets x).length) encIn encUnary :=
    (ComputableInPolyTime.length_list encJet).comp hnodeJets
  let eP1 := encPair encIn encUnary
  have hx := (ComputableInPolyTime.fst encIn encUnary).comp (.fst eP1 encUnary)
  have hi := (ComputableInPolyTime.snd encIn encUnary).comp (.fst eP1 encUnary)
  have hget := (ComputableInPolyTime.listGetD (encA := encJet) []).comp
    ((hnodeJets.comp hx).prod hi)
  exact computableInPolyTime_tabulateTable hr hJ (computableInPolyTime_rowEntry hget
    (.snd eP1 encUnary) (hu.comp hx))

@[fun_prop] theorem computableInPolyTime_extractAllCoordNodeJets {α : Type} {encIn : α ↪ List Bool}
    {J ℓ : α → ℕ} {nodeJets : α → List JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hnodeJets : ComputableInPolyTime nodeJets encIn encJets) :
    ComputableInPolyTime (fun x => extractAllCoordNodeJets (J x) (ℓ x) (nodeJets x))
      encIn encJets := by
  have hfst := ComputableInPolyTime.fst encIn encUnary
  have hbody := computableInPolyTime_extractCoordNodeJets
    (J := fun p : α × ℕ => J p.1) (u := fun p : α × ℕ => p.2) (nodeJets := fun p => nodeJets p.1)
    (hJ.comp hfst) (.snd encIn encUnary) (hnodeJets.comp hfst)
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hℓ) hbody

/-- Truncated `r`-fold product in `ℤ[V]/(V^ℓ)[z]/(z^J)` from `constJet J ℓ 1`
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], eq. (3.11) and Appendix B.2,
p. 49; returns `constJet J ℓ 1` on `[]`). -/
def prodJet (J ℓ : ℕ) (factors : List JetRows) : JetRows :=
  factors.foldl (convJet J ℓ) (constJet J ℓ 1)

@[simp] theorem prodJet_nil (J ℓ : ℕ) : prodJet J ℓ [] = constJet J ℓ 1 := rfl
theorem isTableShape_prodJet (J ℓ : ℕ) (factors : List JetRows) :
    IsTableShape J ℓ (prodJet J ℓ factors) := by
  suffices ∀ {init}, IsTableShape J ℓ init → IsTableShape J ℓ (factors.foldl (convJet J ℓ) init)
    from this (isTableShape_constJet J ℓ 1)
  intro init hinit; induction factors generalizing init with
  | nil => exact hinit
  | cons A _ ih => exact ih (isTableShape_convJet J ℓ init A)
@[simp] theorem toJetTable_prodJet (J ℓ : ℕ) (factors : List JetRows) :
    toJetTable J ℓ (prodJet J ℓ factors) = (factors.map (toJetTable J ℓ)).prod := by
  have h (init : JetRows) : toJetTable J ℓ (factors.foldl (convJet J ℓ) init) =
      toJetTable J ℓ init * (factors.map (toJetTable J ℓ)).prod := by
    induction factors generalizing init with
    | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
    | cons _ _ ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      rw [ih, toJetTable_convJet, mul_assoc]
  rw [prodJet, h, toJetTable_constJet_one, one_mul]
theorem jetL1Norm_prodJet_le (J ℓ : ℕ) (factors : List JetRows) :
    jetL1Norm (prodJet J ℓ factors) ≤ (factors.map jetL1Norm).prod := by
  have h (init : JetRows) : jetL1Norm (factors.foldl (convJet J ℓ) init) ≤
      jetL1Norm init * (factors.map jetL1Norm).prod := by
    induction factors generalizing init with
    | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, Nat.mul_one, le_rfl]
    | cons A _ ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      exact (ih _).trans ((Nat.mul_le_mul_right _ (jetL1Norm_convJet_le J ℓ init A)).trans_eq
        (Nat.mul_assoc _ _ _))
  exact (h (constJet J ℓ 1)).trans
    ((Nat.mul_le_mul_right _ (jetL1Norm_constJet_le J ℓ 1)).trans_eq (Nat.one_mul _))

/-- Product denominator clearing (`prodJet` over `Fin r`) under `∑ g, m_group g = m_test`
(eq. (3.11) and Appendix B.2, p. 49; unconditional in `K`). -/
theorem cast_prodJet_ofFn_cleared {J ℓ r m_test : ℕ} {K : Type*} [CommRing K]
    (Γ : ℤ) (m_group : Fin r → ℕ) (hm : ∑ g : Fin r, m_group g = m_test)
    (S_rat : Fin r → JetTable J ℓ K) (S_int : Fin r → JetRows)
    (hS : ∀ g, (Γ ^ m_group g) • S_rat g = JetTable.castRingHom K (toJetTable J ℓ (S_int g))) :
    (Γ ^ m_test) • (∏ g : Fin r, S_rat g) =
      JetTable.castRingHom K (toJetTable J ℓ (prodJet J ℓ (List.ofFn S_int))) := by
  rw [toJetTable_prodJet, List.map_ofFn, Fin.prod_ofFn]
  exact JetTable.cast_groupProd_cleared Γ m_group hm S_rat (fun g => toJetTable J ℓ (S_int g)) hS

private theorem size_natAbs_foldl_convJet_le {J ℓ b₀ b : ℕ} {factors : List JetRows}
    (hf : ∀ F ∈ factors, ∀ row ∈ F, ∀ z ∈ row, z.natAbs.size ≤ b)
    {init : JetRows} (hinit : ∀ row ∈ init, ∀ z ∈ row, z.natAbs.size ≤ b₀) (j u : ℕ) :
    (rowEntry (factors.foldl (convJet J ℓ) init) j u).natAbs.size ≤
      b₀ + factors.length * (b + (J * ℓ).size) := by
  induction factors generalizing init b₀ with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
    exact rowEntry_rel_of_mem (by simp only [Int.natAbs_zero, Nat.size_zero, Nat.zero_le]) hinit j u
  | cons A _ ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hA := hf A List.mem_cons_self
    have hnext : ∀ row ∈ convJet J ℓ init A, ∀ z ∈ row,
        z.natAbs.size ≤ b₀ + (b + (J * ℓ).size) := fun row hrow z hz => by
      obtain ⟨j', u', rfl⟩ := exists_rowEntry_eq hrow hz
      exact (size_natAbs_rowEntry_convJet_le hinit hA j' u').trans_eq (Nat.add_assoc _ _ _)
    exact (ih (fun F hF => hf F (List.mem_cons_of_mem _ hF)) hnext).trans_eq (by ring)

theorem size_natAbs_rowEntry_prodJet_le {J ℓ b : ℕ} {factors : List JetRows}
    (hf : ∀ F ∈ factors, ∀ row ∈ F, ∀ z ∈ row, z.natAbs.size ≤ b) (j u : ℕ) :
    (rowEntry (prodJet J ℓ factors) j u).natAbs.size ≤
      1 + factors.length * (b + (J * ℓ).size) := by
  refine size_natAbs_foldl_convJet_le hf (fun row hrow z hz => ?_) j u
  obtain ⟨j', u', hj', hu', rfl⟩ := exists_rowEntry_eq_of_mem hrow hz
  have hshape := isTableShape_constJet J ℓ 1
  rw [rowEntry_constJet 1 (hshape.1 ▸ hj') (hshape.2 row hrow ▸ hu')]; split_ifs <;> decide

@[fun_prop] theorem computableInPolyTime_prodJet {α : Type} {encIn : α ↪ List Bool}
    {J ℓ : α → ℕ} {factors : α → List JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hfactors : ComputableInPolyTime factors encIn encJets) :
    ComputableInPolyTime (fun x => prodJet (J x) (ℓ x) (factors x)) encIn encJet := by
  have hinit := computableInPolyTime_constJet hJ hℓ (.const 1)
  let Lf : α → ℕ := fun x => (encJets (factors x)).length
  let B : α → ℕ := fun x => J x * (2 * (ℓ x * (2 * (1 + Lf x * (Lf x + J x * ℓ x)) + 3)) + 1)
  have hJ_pb := hJ.polyBounded; have hℓ_pb := hℓ.polyBounded
  have hLf_pb := hfactors.polyBounded_length
  have hB : PolyBounded (fun x => (encIn x).length) B :=
    hJ_pb.mul (((PolyBounded.const 2).mul (hℓ_pb.mul (((PolyBounded.const 2).mul
      ((PolyBounded.const 1).add (hLf_pb.mul (hLf_pb.add (hJ_pb.mul hℓ_pb))))).add
        (.const 3)))).add (.const 1))
  refine ComputableInPolyTime.foldlWith
    (par := fun x => (J x, ℓ x)) (step := fun p acc A => convJet p.1 p.2 acc A)
    (hJ.prod hℓ) hfactors hinit convJet_polytime hB fun x i _ => ?_
  have hentry : ∀ F ∈ (factors x).take i, ∀ row ∈ F, ∀ z ∈ row, z.natAbs.size ≤ Lf x :=
    fun F hF _ hrow _ hz =>
      (size_natAbs_le_length_encJetRows hrow hz).trans
        (SizedListEncoding.length_elem_le (factors x) F (List.mem_of_mem_take hF))
  have hlist_le : (factors x).length ≤ Lf x :=
    @SizedListEncoding.length_le JetRows encJet _ _ (factors x)
  have hlen_le := (List.length_take_le' i (factors x)).trans hlist_le
  have hsize_JL : (J x * ℓ x).size ≤ J x * ℓ x := Nat.size_le.mpr (J x * ℓ x).lt_two_pow_self
  exact length_encJetRows_le_of_size_le (isTableShape_prodJet _ _ _) fun j _ u _ =>
    (size_natAbs_rowEntry_prodJet_le hentry j u).trans
      (Nat.add_le_add_left (Nat.mul_le_mul hlen_le (Nat.add_le_add_left hsize_JL _)) 1)

/-- Multiply `groups` modulo `(z^J, V^ℓ)` and scale by `w : ℤ` (`zeroJet J ℓ` when `w = 0`;
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], eq. (3.13)). -/
def weightedProdJet (J ℓ : ℕ) (w : ℤ) (groups : List JetRows) : JetRows :=
  smulJet J ℓ w (prodJet J ℓ groups)

theorem isTableShape_weightedProdJet (J ℓ : ℕ) (w : ℤ) (groups : List JetRows) :
    IsTableShape J ℓ (weightedProdJet J ℓ w groups) := isTableShape_smulJet J ℓ w _
@[simp] theorem toJetTable_weightedProdJet (J ℓ : ℕ) (w : ℤ) (groups : List JetRows) :
    toJetTable J ℓ (weightedProdJet J ℓ w groups) = w • (groups.map (toJetTable J ℓ)).prod := by
  rw [weightedProdJet, toJetTable_smulJet, toJetTable_prodJet]
theorem jetL1Norm_weightedProdJet_le (J ℓ : ℕ) (w : ℤ) (groups : List JetRows) :
    jetL1Norm (weightedProdJet J ℓ w groups) ≤ w.natAbs * (groups.map jetL1Norm).prod :=
  (jetL1Norm_smulJet_le J ℓ w _).trans (Nat.mul_le_mul_left w.natAbs (jetL1Norm_prodJet_le J ℓ _))
@[fun_prop] theorem computableInPolyTime_weightedProdJet {α : Type} {encIn : α ↪ List Bool}
    {J ℓ : α → ℕ} {w : α → ℤ} {groups : α → List JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hw : ComputableInPolyTime w encIn encIntBin)
    (hgroups : ComputableInPolyTime groups encIn encJets) :
    ComputableInPolyTime (fun x => weightedProdJet (J x) (ℓ x) (w x) (groups x)) encIn encJet := by
  unfold weightedProdJet; fun_prop

/-! ### Shared additive-fold and `IndexFold` certificate helpers -/

section SharedHelpers

private def rangeAddJet (J ℓ j : ℕ) (f : ℕ → JetRows) : JetRows :=
  (List.range j).foldl (fun acc i => addJet J ℓ acc (f i)) (zeroJet J ℓ)
private theorem isTableShape_rangeAddJet (J ℓ j : ℕ) (f : ℕ → JetRows) :
    IsTableShape J ℓ (rangeAddJet J ℓ j f) := by
  suffices ∀ (xs : List ℕ) {init}, IsTableShape J ℓ init →
      IsTableShape J ℓ (xs.foldl (fun acc x => addJet J ℓ acc (f x)) init) from
    this _ (isTableShape_zeroJet J ℓ)
  intro xs; induction xs with
  | nil => exact id
  | cons x _ ih => intro init h; exact ih (isTableShape_addJet J ℓ init (f x))
private theorem toJetTable_foldl_addJet {ι : Type*} (J ℓ : ℕ) (f : ι → JetRows)
    (xs : List ι) (init : JetRows) :
    toJetTable J ℓ (xs.foldl (fun acc x => addJet J ℓ acc (f x)) init) =
      toJetTable J ℓ init + (xs.map fun x => toJetTable J ℓ (f x)).sum := by
  induction xs generalizing init with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons _ _ ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih, toJetTable_addJet, add_assoc]
private theorem toJetTable_rangeAddJet (J ℓ j : ℕ) (f : ℕ → JetRows) :
    toJetTable J ℓ (rangeAddJet J ℓ j f) = ∑ i ∈ Finset.range j, toJetTable J ℓ (f i) := by
  rw [rangeAddJet, toJetTable_foldl_addJet, toJetTable_zeroJet, zero_add, List.sum_map_range]
  exact Fin.sum_univ_eq_sum_range (fun i => toJetTable J ℓ (f i)) j
private theorem natAbs_rowEntry_rangeAddJet_le (J ℓ j M : ℕ) (f : ℕ → JetRows)
    (hf : ∀ i < j, ∀ j' < J, ∀ u' < ℓ, (rowEntry (f i) j' u').natAbs ≤ M) (j' u' : ℕ) :
    (rowEntry (rangeAddJet J ℓ j f) j' u').natAbs ≤ j * M := by
  by_cases hju : j' < J ∧ u' < ℓ
  · obtain ⟨hj', hu'⟩ := hju
    induction j with
    | zero =>
      simp only [rangeAddJet, List.range_zero, List.foldl_nil, rowEntry_zeroJet, Int.natAbs_zero,
        Nat.zero_mul, le_rfl]
    | succ k ih =>
      simp only [rangeAddJet, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [rowEntry_addJet _ _ hj' hu']
      exact (Int.natAbs_add_le _ _).trans
        ((Nat.add_le_add (ih fun i hi => hf i (by omega)) (hf k (by omega) j' hj' u' hu')).trans_eq
          (by ring))
  · rw [rowEntry_eq_zero_of_isTableShape (isTableShape_rangeAddJet J ℓ j f) hju]
    simp only [Int.natAbs_zero, Nat.zero_le]
private theorem length_encJetRows_rangeAddJet_le {J ℓ j N M : ℕ} {f : ℕ → JetRows}
    (hj : j ≤ N) (hM : ∀ i < j, ∀ j' < J, ∀ u' < ℓ, (rowEntry (f i) j' u').natAbs ≤ M) :
    (encJet (rangeAddJet J ℓ j f)).length ≤ J * (2 * (ℓ * (2 * (N.size + M.size) + 3)) + 1) :=
  length_encJetRows_le_of_size_le (isTableShape_rangeAddJet J ℓ j f) fun j' _ u' _ =>
    (Nat.size_le_size ((natAbs_rowEntry_rangeAddJet_le J ℓ j M f hM j' u').trans
      (Nat.mul_le_mul_right M hj))).trans (Nat.size_mul_le N M)

/-- A native certificate `c` has polynomially bounded workspace in the encoded input length. -/
def HasPolySpace {α β : Type} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    {f : α → β} (c : NativeCertificate f ei eo) : Prop :=
  PolyBounded (fun a => (ei a).length) c.space
theorem polyBounded_length_of_hasPolySpace {α β : Type} {ei : α ↪ List Bool}
    {eo : β ↪ List Bool} {f : α → β} {c : NativeCertificate f ei eo} (hc : HasPolySpace c) :
    PolyBounded (fun a => (ei a).length) (fun a => (eo (f a)).length) := by
  obtain ⟨c₀, d₀, hs⟩ := hc.exists_le
  obtain ⟨k, _, hl⟩ := c.computes
  refine .of_forall_le (k * (c₀ + 1)) d₀ fun a => (hl a).trans ?_
  have h1 : 1 ≤ ((ei a).length + 1) ^ d₀ := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have := hs a; nlinarith
theorem hasPolySpace_comp {α β γ : Type} {ei : α ↪ List Bool} {em : β ↪ List Bool}
    {eo : γ ↪ List Bool} {f : α → β} {g : β → γ} {d : NativeCertificate g em eo}
    {c : NativeCertificate f ei em} (hd : HasPolySpace d) (hc : HasPolySpace c) :
    HasPolySpace (d.comp c) := hc.add (hd.comp (polyBounded_length_of_hasPolySpace hc))
theorem hasPolySpace_prod {α β γ : Type} {ei : α ↪ List Bool} {em : β ↪ List Bool}
    {eo : γ ↪ List Bool} {f : α → β} {g : α → γ} {c : NativeCertificate f ei em}
    {d : NativeCertificate g ei eo} (hc : HasPolySpace c) (hd : HasPolySpace d) :
    HasPolySpace (c.prod d) := hc.add hd
private theorem exists_cert_of_polySpace {α β : Type} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    {f : α → β} (h : ComputableInPolySpace f ei eo) :
    ∃ c : NativeCertificate f ei eo, HasPolySpace c := by
  obtain ⟨t, s, hs, hc, hl⟩ := h
  exact ⟨⟨t, fun a => s (ei a).length, 1,
    hc.mono (fun _ => by omega) (fun _ => by dsimp only; omega),
    fun a => (hl a).trans (by dsimp only; omega)⟩,
    .of_polynomiallyBounded (fun a => (ei a).length) hs⟩
private theorem computableInPolySpace_of_inO {α β : Type} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    {f : α → β} {T P : α → ℕ} (hP : PolyBounded (fun x => (ei x).length) P)
    (hc : ComputableInO f ei eo T P) : ComputableInPolySpace f ei eo := by
  obtain ⟨c₀, d₀, hPb⟩ := hP.exists_le
  obtain ⟨k, htm, hl⟩ := hc
  let b (n : ℕ) := k * (c₀ * (n + 1) ^ d₀ + 1)
  have hk (x : α) : k * (P x + 1) ≤ b (ei x).length :=
    Nat.mul_le_mul_left k (Nat.add_le_add_right (hPb x) 1)
  exact ⟨_, b, by dsimp only [b]; fun_prop, htm.mono (fun _ => le_rfl) hk,
    fun x => (hl x).trans (hk x)⟩
private theorem pb_aff {ι : Type} {sz f g : ι → ℕ} (a b c : ℕ)
    (hf : PolyBounded sz f) (hg : PolyBounded sz g) :
    PolyBounded sz (fun x => a * f x + b * g x + c) :=
  (((PolyBounded.const a).mul hf).add ((PolyBounded.const b).mul hg)).add (.const c)
private theorem polyBounded_jetEncBound {ι : Type} {sz J ℓ K M : ι → ℕ}
    (hJ : PolyBounded sz J) (hℓ : PolyBounded sz ℓ) (hK : PolyBounded sz K)
    (hM : PolyBounded sz M) :
    PolyBounded sz (fun x => J x * (2 * (ℓ x * (2 * (K x + M x) + 3)) + 1)) :=
  hJ.mul (((PolyBounded.const 2).mul (hℓ.mul
    (((PolyBounded.const 2).mul (hK.add hM)).add (.const 3)))).add (.const 1))
theorem exists_natAbs_rowEntry_le_two_pow {ι γ : Type} {sz : ι → ℕ}
    {encΓ : γ ↪ List Bool} {f : γ → JetRows} {L : ι → ℕ}
    (hf : PolyBounded (fun y => (encΓ y).length) (fun y => (encJet (f y)).length))
    (hL : PolyBounded sz L) :
    ∃ M : ι → ℕ, PolyBounded sz M ∧
      ∀ x y, (encΓ y).length ≤ L x → ∀ j u, (rowEntry (f y) j u).natAbs ≤ 2 ^ M x := by
  obtain ⟨c, d, hle⟩ := hf.exists_le
  refine ⟨fun x => c * (L x + 1) ^ d, NativeCertificate.polyBounded_pow_of_polyBounded hL c d,
    fun x y hy j u => ?_⟩
  have hout := (hle y).trans
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hy 1) d))
  exact (Nat.size_le.mp ((size_natAbs_rowEntry_le_length_encJetRows (f y) j u).trans hout)).le

theorem computableInO_snd_indexFold {ι β : Type} {encIn : ι ↪ List Bool}
    {encB : β ↪ List Bool} {count : ι → ℕ} {initial : ι → β} {body : ℕ × β → β}
    (cn : NativeCertificate count encIn encNat) (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body (encPair encNat encB) encB)
    (hcn : cn.IsPolynomial) (hci : ci.IsPolynomial) (hcb : HasPolySpace cb)
    {B : ι → ℕ} (hB_pb : PolyBounded (fun x => (encIn x).length) B)
    (hB : ∀ x j, j ≤ count x → (encB (IndexFold.run body j (initial x)).2).length ≤ B x)
    (R P_cb : ι → ℕ) (hP_cb : PolyBounded (fun x => (encIn x).length) P_cb)
    (hR : ∀ x j, j ≤ count x →
      (encPair encNat encB (IndexFold.run body j (initial x))).length ≤
        2 * (encNat (count x)).length + 1 + B x →
      cb.time (IndexFold.run body j (initial x)) ≤ R x + P_cb x) :
    ∃ P : ι → ℕ, PolyBounded (fun x => (encIn x).length) P ∧
      ComputableInO (fun x => (IndexFold.run body (count x) (initial x)).2) encIn encB
        (fun x => (count x + 1) * (R x + P x)) P := by
  have hcnt_pb := (cn.polyTime hcn).polyBounded_length
  let S_st : ι → ℕ := fun x => 2 * (encNat (count x)).length + 1 + B x
  have hSst_pb := (((PolyBounded.const 2).mul hcnt_pb).add (.const 1)).add hB_pb
  obtain ⟨cs, ds, hcs⟩ := hcb.exists_le
  let Q : ι → ℕ := fun x => cs * (S_st x + 1) ^ ds
  have hQ_pb := NativeCertificate.polyBounded_pow_of_polyBounded hSst_pb cs ds
  have hsq_pb := NativeCertificate.polyBounded_pow_of_polyBounded hcnt_pb 1 2
  have hloop := IndexFold.computableInO cn ci cb (fun x => R x + P_cb x) Q B
    (fun x j hj => hR x j hj (IndexFold.length_run_le body (initial x) hj (hB x j hj)))
    (fun x j hj => (hcs _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left
      (Nat.add_le_add_right (IndexFold.length_run_le body (initial x) hj (hB x j hj)) 1) ds))) hB
  let cLoop : NativeCertificate (fun x => IndexFold.run body (count x) (initial x))
      encIn (encPair encNat encB) := ⟨_, _, hloop⟩
  let P : ι → ℕ := fun x => cn.time x + cn.space x + (encIn x).length + ci.time x + ci.space x +
    2 * S_st x + 2 * (1 * ((encNat (count x)).length + 1) ^ 2) + P_cb x + Q x +
    2 * (encNat (count x)).length + 1
  have hP_pb : PolyBounded (fun x => (encIn x).length) P :=
    ((((((((((hcn.1.add hcn.2).add .self).add hci.1).add hci.2).add
      ((PolyBounded.const 2).mul hSst_pb)).add ((PolyBounded.const 2).mul hsq_pb)).add
      hP_cb).add hQ_pb).add ((PolyBounded.const 2).mul hcnt_pb)).add (.const 1))
  refine ⟨P, hP_pb, (NativeCertificate.snd cLoop).computes.mono_le (fun x => ?_) (fun x => ?_)⟩
  · have hinit_le := Nat.le_mul_of_pos_left (cn.time x + ((encIn x).length + ci.time x))
      (Nat.succ_pos (count x))
    have hstep_le : (S_st x + ((encNat (count x)).length + 1) ^ 2 + (R x + P_cb x)) +
        S_st x + ((encNat (count x)).length + 1) ^ 2 ≤
        R x + (2 * S_st x + 2 * (1 * ((encNat (count x)).length + 1) ^ 2) + P_cb x) := by omega
    have hmul_le := Nat.add_le_add hinit_le (Nat.mul_le_mul_left (count x + 1) hstep_le)
    rw [← Nat.mul_add] at hmul_le
    exact hmul_le.trans (Nat.mul_le_mul_left (count x + 1) (by dsimp only [P]; omega))
  · dsimp only [NativeCertificate.snd_space, cLoop, S_st, P]; omega

section AccumStep

variable {ι α ω ρ : Type} {encIn : ι ↪ List Bool} {encCtx : α ↪ List Bool}
  {encΩ : ω ↪ List Bool} {encΡ : ρ ↪ List Bool}

/-- Initial loop-state certificate pairing `((J, ℓ), ctx)` with `zeroJet J ℓ`. -/
noncomputable def initJetStateCertificate {J ℓ : ι → ℕ} {ctx : ι → α}
    (cJ : NativeCertificate J encIn encUnary) (cℓ : NativeCertificate ℓ encIn encUnary)
    (cctx : NativeCertificate ctx encIn encCtx) :
    NativeCertificate (fun x => (((J x, ℓ x), ctx x), zeroJet (J x) (ℓ x))) encIn
      (encAccum(encCtx)) :=
  (((cJ.prod cℓ).prod cctx).prod
    ((NativeCertificate.ofPolyTime zeroJet_polytime).comp (cJ.prod cℓ)))
private theorem initJetStateCertificate_isPolynomial {J ℓ : ι → ℕ} {ctx : ι → α}
    {cJ : NativeCertificate J encIn encUnary} {cℓ : NativeCertificate ℓ encIn encUnary}
    {cctx : NativeCertificate ctx encIn encCtx}
    (hcJ : cJ.IsPolynomial) (hcℓ : cℓ.IsPolynomial) (hcctx : cctx.IsPolynomial) :
    (initJetStateCertificate cJ cℓ cctx).IsPolynomial :=
  NativeCertificate.prod_isPolynomial _ _ (NativeCertificate.prod_isPolynomial _ _
    (NativeCertificate.prod_isPolynomial _ _ hcJ hcℓ) hcctx)
    (NativeCertificate.comp_isPolynomial _ _ (NativeCertificate.ofPolyTime_isPolynomial _)
      (NativeCertificate.prod_isPolynomial _ _ hcJ hcℓ))

theorem prepareAccumEval_polyTime :
    ComputableInPolyTime (fun p : ω × (((ℕ × ℕ) × α) × JetRows) => (p.2.1.2, p.1))
      (encPair encΩ (encAccum(encCtx))) (encPair encCtx encΩ) := by fun_prop
/-- Polynomial-time combinator predicate for encoded accumulator updates. -/
abbrev CombPoly (combine : (ℕ × ℕ) → JetRows → ρ → JetRows) (encΡ : ρ ↪ List Bool) : Prop :=
  ComputableInPolyTime (fun r : ((ℕ × ℕ) × JetRows) × ρ => combine r.1.1 r.1.2 r.2)
    (encPair (encPair encDims encJet) encΡ) encJet

theorem applyAccumCombine_polyTime (combine : (ℕ × ℕ) → JetRows → ρ → JetRows)
    (hcomb : CombPoly combine encΡ) :
    ComputableInPolyTime
      (fun q : (ω × (((ℕ × ℕ) × α) × JetRows)) × ρ => combine q.1.2.1.1 q.1.2.2 q.2)
      (encPair (encPair encΩ (encAccum(encCtx))) encΡ) encJet := by
  have harg : ComputableInPolyTime (fun q : (ω × (((ℕ × ℕ) × α) × JetRows)) × ρ =>
      ((q.1.2.1.1, q.1.2.2), q.2)) (encPair (encPair encΩ (encAccum(encCtx))) encΡ)
      (encPair (encPair encDims encJet) encΡ) := by fun_prop
  exact hcomb.comp harg

/-- Generic single-step `NativeCertificate` updating the `JetRows` accumulator component. -/
noncomputable def accumStepBodyCertificate (combine : (ℕ × ℕ) → JetRows → ρ → JetRows)
    (hcomb : CombPoly combine encΡ) {cb_eval : α × ω → ρ}
    (ceval : NativeCertificate cb_eval (encPair encCtx encΩ) encΡ) :
    NativeCertificate (fun p : ω × (((ℕ × ℕ) × α) × JetRows) =>
      (p.2.1, combine p.2.1.1 p.2.2 (cb_eval (p.2.1.2, p.1))))
      (encPair encΩ (encAccum(encCtx))) (encAccum(encCtx)) :=
  (NativeCertificate.linear ((ComputableInO.fst (encPair encDims encCtx) encJet).comp_linear
    (ComputableInO.snd encΩ (encAccum(encCtx))))).prod
    ((NativeCertificate.ofPolyTime (applyAccumCombine_polyTime combine hcomb)).comp
      ((NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)).prod
        (ceval.comp (NativeCertificate.ofPolyTime prepareAccumEval_polyTime))))
private theorem accumStepBodyCertificate_isPolynomial (combine : (ℕ × ℕ) → JetRows → ρ → JetRows)
    (hcomb : CombPoly combine encΡ) {cb_eval : α × ω → ρ}
    {ceval : NativeCertificate cb_eval (encPair encCtx encΩ) encΡ} (hceval : ceval.IsPolynomial) :
    (accumStepBodyCertificate combine hcomb ceval).IsPolynomial :=
  NativeCertificate.prod_isPolynomial _ _ (NativeCertificate.linear_isPolynomial _)
    (NativeCertificate.comp_isPolynomial _ _ (NativeCertificate.ofPolyTime_isPolynomial _)
      (NativeCertificate.prod_isPolynomial _ _ (NativeCertificate.linear_isPolynomial _)
        (NativeCertificate.comp_isPolynomial _ _ hceval
          (NativeCertificate.ofPolyTime_isPolynomial _))))
private theorem hasPolySpace_accumStepBodyCertificate (combine : (ℕ × ℕ) → JetRows → ρ → JetRows)
    (hcomb : CombPoly combine encΡ) {cb_eval : α × ω → ρ}
    {ceval : NativeCertificate cb_eval (encPair encCtx encΩ) encΡ} (hceval : HasPolySpace ceval) :
    HasPolySpace (accumStepBodyCertificate combine hcomb ceval) :=
  hasPolySpace_prod .self (hasPolySpace_comp (NativeCertificate.ofPolyTime_isPolynomial _).2
    (hasPolySpace_prod .self (hasPolySpace_comp hceval
      (NativeCertificate.ofPolyTime_isPolynomial _).2)))
private theorem exists_accumStepBodyCertificate_time_le (combine : (ℕ × ℕ) → JetRows → ρ → JetRows)
    (hcomb : CombPoly combine encΡ) {cb_eval : α × ω → ρ}
    {ceval : NativeCertificate cb_eval (encPair encCtx encΩ) encΡ} (hceval : HasPolySpace ceval) :
    ∃ c_b d_b : ℕ, ∀ st : ω × (((ℕ × ℕ) × α) × JetRows),
      (accumStepBodyCertificate combine hcomb ceval).time st ≤ ceval.time (st.2.1.2, st.1) +
        c_b * ((encPair encΩ (encAccum(encCtx)) st).length + 1) ^ d_b := by
  let cPrep := NativeCertificate.ofPolyTime
    (prepareAccumEval_polyTime (encCtx := encCtx) (encΩ := encΩ))
  let cComb := NativeCertificate.ofPolyTime
    (applyAccumCombine_polyTime (encCtx := encCtx) (encΩ := encΩ) combine hcomb)
  let hcPrep := NativeCertificate.ofPolyTime_isPolynomial
    (prepareAccumEval_polyTime (encCtx := encCtx) (encΩ := encΩ))
  let hcComb := NativeCertificate.ofPolyTime_isPolynomial
    (applyAccumCombine_polyTime (encCtx := encCtx) (encΩ := encΩ) combine hcomb)
  have hcArg_sp : HasPolySpace
      ((NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)).prod (ceval.comp cPrep)) :=
    hasPolySpace_prod .self (hasPolySpace_comp hceval hcPrep.2)
  have hover_pb : PolyBounded (fun st => (encPair encΩ (encAccum(encCtx)) st).length)
      (fun st => 2 * (encPair encΩ (encAccum(encCtx)) st).length + cPrep.time st +
        cComb.time (st, cb_eval (st.2.1.2, st.1))) :=
    (((PolyBounded.const 2).mul .self).add hcPrep.1).add
      (hcComb.1.comp (polyBounded_length_of_hasPolySpace hcArg_sp))
  obtain ⟨c_b, d_b, hle⟩ := hover_pb.exists_le
  refine ⟨c_b, d_b, fun st => ?_⟩
  have h := hle st
  simp only [accumStepBodyCertificate, NativeCertificate.prod_time, NativeCertificate.comp_time,
    NativeCertificate.linear_time, Function.comp_apply]
  dsimp only [cPrep, cComb] at h; omega

end AccumStep

end SharedHelpers

/-! ### 2. Streaming local-Boolean group sum (`streamGroupJetSum`) -/

section GroupJetSum

variable {ι α : Type} {encIn : ι ↪ List Bool} {encCtx : α ↪ List Bool}

section Spec
variable (evalGroupProd : α × (ℕ × List Bool) → JetRows)

/-- Single-assignment body for `streamGroupJetSum`: retains `((J, ℓ), ctx)` and adds
`evalGroupProd (ctx, wd)` via `addJet`. -/
def groupSumBody (p : (ℕ × List Bool) × (((ℕ × ℕ) × α) × JetRows)) : ((ℕ × ℕ) × α) × JetRows :=
  (p.2.1, addJet p.2.1.1.1 p.2.1.1.2 p.2.2 (evalGroupProd (p.2.1.2, p.1)))

/-- Live `(J × ℓ)` jet accumulator after visiting the first `j` local-Boolean assignments. -/
def streamGroupJetSumPrefix (J ℓ d j : ℕ) (ctx : α) : JetRows :=
  (BooleanFold.runPrefix (groupSumBody evalGroupProd) d j (((J, ℓ), ctx), zeroJet J ℓ)).2.2.2

/-- Streaming local-Boolean group sum over all `2 ^ d` assignments of unary dimension `d` via
`BooleanFold.run` ([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma 3.2,
Proposition 3.4, and Appendix B.2, p. 49). -/
def streamGroupJetSum (J ℓ d : ℕ) (ctx : α) : JetRows :=
  (BooleanFold.run (groupSumBody evalGroupProd) d (((J, ℓ), ctx), zeroJet J ℓ)).2.2.2

private theorem streamGroupJetSumRunPrefix_snd_snd_foldl (J ℓ d j : ℕ) (ctx : α) :
    (BooleanFold.runPrefix (groupSumBody evalGroupProd) d j (((J, ℓ), ctx), zeroJet J ℓ)).2.2 =
      (((J, ℓ), ctx), rangeAddJet J ℓ j fun i => evalGroupProd (ctx, (d, lowBits d i))) :=
  (BooleanFold.prefix_accumulator (groupSumBody evalGroupProd) d j _).trans
    (List.foldl_keep_fst (fun (par : (ℕ × ℕ) × α) acc i =>
      addJet par.1.1 par.1.2 acc (evalGroupProd (par.2, (d, lowBits d i))))
      ((J, ℓ), ctx) (List.range j) (zeroJet J ℓ))
theorem streamGroupJetSumPrefix_eq_foldl (J ℓ d j : ℕ) (ctx : α) :
    streamGroupJetSumPrefix evalGroupProd J ℓ d j ctx =
      (List.range j).foldl
        (fun acc i => addJet J ℓ acc (evalGroupProd (ctx, (d, lowBits d i)))) (zeroJet J ℓ) :=
  congrArg Prod.snd (streamGroupJetSumRunPrefix_snd_snd_foldl evalGroupProd J ℓ d j ctx)
theorem toJetTable_streamGroupJetSum_eq_sum (J ℓ d : ℕ) (ctx : α) :
    toJetTable J ℓ (streamGroupJetSum evalGroupProd J ℓ d ctx) =
      ∑ x : BitString d, toJetTable J ℓ (evalGroupProd (ctx, (d, List.ofFn x))) := by
  have hfold : streamGroupJetSum evalGroupProd J ℓ d ctx =
      (enumList d).foldl (fun acc w => addJet J ℓ acc (evalGroupProd (ctx, (d, w))))
        (zeroJet J ℓ) :=
    congrArg Prod.snd ((BooleanFold.run_accumulator (groupSumBody evalGroupProd) d _).trans
      (List.foldl_keep_fst (fun (par : (ℕ × ℕ) × α) acc w =>
        addJet par.1.1 par.1.2 acc (evalGroupProd (par.2, (d, w))))
        ((J, ℓ), ctx) (enumList d) (zeroJet J ℓ)))
  rw [hfold, toJetTable_foldl_addJet, toJetTable_zeroJet, zero_add, enumList, List.map_map,
    Function.comp_def, ← List.sum_toFinset _ (nodup_enum d)]
  have hall : (enum d).toFinset = Finset.univ := by
    ext x; simp only [List.mem_toFinset, mem_enum, Finset.mem_univ]
  rw [hall]
theorem isTableShape_streamGroupJetSumPrefix (J ℓ d j : ℕ) (ctx : α) :
    IsTableShape J ℓ (streamGroupJetSumPrefix evalGroupProd J ℓ d j ctx) := by
  rw [streamGroupJetSumPrefix_eq_foldl]; exact isTableShape_rangeAddJet J ℓ j _
theorem isTableShape_streamGroupJetSum (J ℓ d : ℕ) (ctx : α) :
    IsTableShape J ℓ (streamGroupJetSum evalGroupProd J ℓ d ctx) :=
  isTableShape_streamGroupJetSumPrefix evalGroupProd J ℓ d (2 ^ d) ctx

/-- All-prefix encoded bit-length bound for `streamGroupJetSumPrefix` (Appendix B.2, p. 49). -/
theorem length_encJetRows_streamGroupJetSumPrefix_le {J ℓ d j M_group : ℕ} (ctx : α)
    (hj : j ≤ 2 ^ d) (hM : ∀ word, word.length = d → ∀ j' < J, ∀ u' < ℓ,
      (rowEntry (evalGroupProd (ctx, (d, word))) j' u').natAbs ≤ M_group) :
    (encJet (streamGroupJetSumPrefix evalGroupProd J ℓ d j ctx)).length ≤
      J * (2 * (ℓ * (2 * (d + 1 + M_group.size) + 3)) + 1) := by
  rw [streamGroupJetSumPrefix_eq_foldl, ← Nat.size_pow (n := d)]
  exact length_encJetRows_rangeAddJet_le hj fun i _ => hM _ (length_lowBits d i)

end Spec

/-- Fixed-denominator clearing for `streamGroupJetSum` (Appendix B.2, p. 49, in `CommRing K`). -/
theorem cast_streamGroupJetSum_cleared {J ℓ d m_g : ℕ} {K : Type*} [CommRing K]
    (Γ : ℤ) (evalGroupProd : α × (ℕ × List Bool) → JetRows) (ctx : α)
    (A_rat : BitString d → JetTable J ℓ K)
    (hA : ∀ x : BitString d, (Γ ^ m_g) • A_rat x =
      JetTable.castRingHom K (toJetTable J ℓ (evalGroupProd (ctx, (d, List.ofFn x))))) :
    (Γ ^ m_g) • (∑ x : BitString d, A_rat x) =
      JetTable.castRingHom K (toJetTable J ℓ (streamGroupJetSum evalGroupProd J ℓ d ctx)) := by
  rw [toJetTable_streamGroupJetSum_eq_sum, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ => hA x

/-- Lemma 3.2 cross-group distributive factorization ([OpenAI, *The Exponential Time Hypothesis is
False*][OpenAI2026ETH], §3.3, pp. 22–23). -/
theorem toJetTable_prodJet_streamGroupJetSum {J ℓ r : ℕ} (d : Fin r → ℕ)
    (evalGroup : Fin r → (α × (ℕ × List Bool) → JetRows)) (ctx : α) :
    toJetTable J ℓ
        (prodJet J ℓ (List.ofFn fun g => streamGroupJetSum (evalGroup g) J ℓ (d g) ctx)) =
      ∑ x : ∀ g : Fin r, BitString (d g),
        ∏ g : Fin r, toJetTable J ℓ (evalGroup g (ctx, (d g, List.ofFn (x g)))) := by
  rw [toJetTable_prodJet, List.map_ofFn, Fin.prod_ofFn]
  simp only [Function.comp_def, toJetTable_streamGroupJetSum_eq_sum]
  exact Fintype.prod_sum fun g y => toJetTable J ℓ (evalGroup g (ctx, (d g, List.ofFn y)))

theorem combineGroupAdd_polyTime : ComputableInPolyTime
    (fun r : ((ℕ × ℕ) × JetRows) × JetRows => addJet r.1.1.1 r.1.1.2 r.1.2 r.2)
    (encPair (encPair encDims encJet) encJet) encJet := by fun_prop

/-- Single-step `BooleanFold` body certificate for `streamGroupJetSum`. -/
noncomputable abbrev groupSumBodyCertificate {evalGroupProd : α × (ℕ × List Bool) → JetRows}
    (cprod : NativeCertificate evalGroupProd (encPair encCtx (encPair encUnary encBits)) encJet) :
    NativeCertificate (groupSumBody evalGroupProd)
      (encPair (encPair encUnary encBits) (encAccum(encCtx))) (encAccum(encCtx)) :=
  accumStepBodyCertificate (ρ := JetRows)
    (fun p acc y => addJet p.1 p.2 acc y) combineGroupAdd_polyTime cprod

/-- Uniform `NativeCertificate` for `streamGroupJetSum`, built via `BooleanFold.certificate`. -/
noncomputable def groupJetSumCertificate {J ℓ d : ι → ℕ} {ctx : ι → α}
    {evalGroupProd : α × (ℕ × List Bool) → JetRows}
    (cJ : NativeCertificate J encIn encUnary) (cℓ : NativeCertificate ℓ encIn encUnary)
    (cd : NativeCertificate d encIn encUnary) (cctx : NativeCertificate ctx encIn encCtx)
    (cprod : NativeCertificate evalGroupProd (encPair encCtx (encPair encUnary encBits)) encJet) :
    NativeCertificate (fun x => streamGroupJetSum evalGroupProd (J x) (ℓ x) (d x) (ctx x))
      encIn encJet :=
  NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.snd
    (BooleanFold.certificate cd (initJetStateCertificate cJ cℓ cctx)
      (groupSumBodyCertificate cprod))))

private theorem groupJetSum_run_inO {J ℓ d : ι → ℕ} {ctx : ι → α}
    {evalGroupProd : α × (ℕ × List Bool) → JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary) (hctx : ComputableInPolyTime ctx encIn encCtx)
    {cprod : NativeCertificate evalGroupProd (encPair encCtx (encPair encUnary encBits)) encJet}
    (hcprod_sp : HasPolySpace cprod) (R : ι → ℕ) (ct dt : ℕ)
    (hR : ∀ x j, j ≤ 2 ^ d x → (BooleanFold.visitCertificate (groupSumBodyCertificate cprod)).time
      (BooleanFold.runPrefix (groupSumBody evalGroupProd) (d x) j
        (((J x, ℓ x), ctx x), zeroJet (J x) (ℓ x))) ≤
      R x + ct * ((encPair encNat (encPair encUnary (encAccum(encCtx)))
        (BooleanFold.runPrefix (groupSumBody evalGroupProd) (d x) j
          (((J x, ℓ x), ctx x), zeroJet (J x) (ℓ x)))).length + 1) ^ dt) :
    ∃ P : ι → ℕ, PolyBounded (fun x => (encIn x).length) P ∧
      ComputableInO (fun x => streamGroupJetSum evalGroupProd (J x) (ℓ x) (d x) (ctx x))
        encIn encJet (fun x => (2 ^ d x + 1) * (R x + P x)) P := by
  have hJ_pb := hJ.polyBounded; have hℓ_pb := hℓ.polyBounded
  have hd_pb := hd.polyBounded; have hctx_pb := hctx.polyBounded_length
  obtain ⟨M_bits, hM_pb, hM_le⟩ := exists_natAbs_rowEntry_le_two_pow
    (polyBounded_length_of_hasPolySpace hcprod_sp) (pb_aff 2 3 2 hctx_pb hd_pb)
  let B_acc : ι → ℕ := fun x => J x * (2 * (ℓ x * (2 * ((d x + 1) + (M_bits x + 1)) + 3)) + 1)
  have hBacc_pb := polyBounded_jetEncBound hJ_pb hℓ_pb (hd_pb.add (.const 1)) (hM_pb.add (.const 1))
  let B_inner : ι → ℕ := fun x =>
    (10 * d x + 8 * J x + 0) + (4 * ℓ x + 2 * (encCtx (ctx x)).length + 8) + B_acc x
  have hBinner_pb : PolyBounded (fun x => (encIn x).length) B_inner :=
    ((pb_aff 10 8 0 hd_pb hJ_pb).add (pb_aff 4 2 8 hℓ_pb hctx_pb)).add hBacc_pb
  have hB : ∀ x j, j ≤ 2 ^ d x → (encPair encUnary (encAccum(encCtx))
      (BooleanFold.runPrefix (groupSumBody evalGroupProd) (d x) j
        (((J x, ℓ x), ctx x), zeroJet (J x) (ℓ x))).2).length ≤ B_inner x := fun x j hj => by
    have hacc_len :
        (encJet (streamGroupJetSumPrefix evalGroupProd (J x) (ℓ x) (d x) j (ctx x))).length ≤
          B_acc x := by
      have h := length_encJetRows_streamGroupJetSumPrefix_le evalGroupProd
        (J := J x) (ℓ := ℓ x) (M_group := 2 ^ M_bits x) (ctx x) hj fun word hw j' _ u' _ =>
          hM_le x (ctx x, (d x, word)) (by
            simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply, hw]
            omega) j' u'
      rwa [Nat.size_pow] at h
    have hw := BooleanFold.prefix_width (groupSumBody evalGroupProd) (d x) j
      (((J x, ℓ x), ctx x), zeroJet (J x, ℓ x).1 (J x, ℓ x).2)
    have hf := congrArg Prod.fst
      (streamGroupJetSumRunPrefix_snd_snd_foldl evalGroupProd (J x) (ℓ x) (d x) j (ctx x))
    have hpair : (BooleanFold.runPrefix (groupSumBody evalGroupProd) (d x) j
        (((J x, ℓ x), ctx x), zeroJet (J x) (ℓ x))).2 =
        (d x, (((J x, ℓ x), ctx x),
          streamGroupJetSumPrefix evalGroupProd (J x) (ℓ x) (d x) j (ctx x))) :=
      Prod.ext hw (Prod.ext hf rfl)
    rw [hpair]; dsimp only [B_inner, B_acc] at hacc_len ⊢
    simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
  have hcd := NativeCertificate.ofPolyTime_isPolynomial hd
  have hclk_poly := NativeCertificate.comp_isPolynomial BooleanFold.clock (.ofPolyTime hd)
    ⟨.self, .self⟩ hcd
  have hcnt_pb := ((BooleanFold.clock.comp (.ofPolyTime hd)).polyTime hclk_poly).polyBounded_length
  let S_st : ι → ℕ := fun x => 2 * (encNat (2 ^ d x)).length + 1 + B_inner x
  have hSst_pb := (((PolyBounded.const 2).mul hcnt_pb).add (.const 1)).add hBinner_pb
  have hvisit_sp : HasPolySpace (BooleanFold.visitCertificate (groupSumBodyCertificate cprod)) :=
    hasPolySpace_prod .self (hasPolySpace_comp (hasPolySpace_accumStepBodyCertificate
      (fun p acc y => addJet p.1 p.2 acc y) combineGroupAdd_polyTime hcprod_sp)
      (NativeCertificate.ofPolyTime_isPolynomial _).2)
  obtain ⟨P, hP_pb, hcomp⟩ := computableInO_snd_indexFold
    (BooleanFold.clock.comp (.ofPolyTime hd))
    ((NativeCertificate.ofPolyTime hd).prod
      (initJetStateCertificate (.ofPolyTime hJ) (.ofPolyTime hℓ) (.ofPolyTime hctx)))
    (BooleanFold.visitCertificate (groupSumBodyCertificate cprod)) hclk_poly
    (NativeCertificate.prod_isPolynomial _ _ hcd (initJetStateCertificate_isPolynomial
      (NativeCertificate.ofPolyTime_isPolynomial hJ) (NativeCertificate.ofPolyTime_isPolynomial hℓ)
      (NativeCertificate.ofPolyTime_isPolynomial hctx)))
    hvisit_sp hBinner_pb hB R (fun x => ct * (S_st x + 1) ^ dt)
    (NativeCertificate.polyBounded_pow_of_polyBounded hSst_pb ct dt) fun x j hj hst_len =>
      (hR x j hj).trans (Nat.add_le_add_left
        (Nat.mul_le_mul_left ct (Nat.pow_le_pow_left (Nat.add_le_add_right hst_len 1) dt)) _)
  let cRes : NativeCertificate _ encIn _ := ⟨_, _, hcomp⟩
  exact ⟨P, hP_pb, (NativeCertificate.snd (NativeCertificate.snd cRes)).computes⟩

/-- Explicit `ComputableInO` time `O((2 ^ d + 1) * P)` and space `O(P)` bound for
`streamGroupJetSum`. -/
theorem computableInO_streamGroupJetSum {J ℓ d : ι → ℕ} {ctx : ι → α}
    {evalGroupProd : α × (ℕ × List Bool) → JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary) (hctx : ComputableInPolyTime ctx encIn encCtx)
    (hprod : ComputableInPolyTime evalGroupProd
      (encPair encCtx (encPair encUnary encBits)) encJet) :
    ∃ P : ι → ℕ, PolyBounded (fun x => (encIn x).length) P ∧
      ComputableInO (fun x => streamGroupJetSum evalGroupProd (J x) (ℓ x) (d x) (ctx x))
        encIn encJet (fun x => (2 ^ d x + 1) * P x) P := by
  have hcprod := NativeCertificate.ofPolyTime_isPolynomial hprod
  obtain ⟨ct, dt, hvt⟩ := (BooleanFold.visitCertificate_isPolynomial _
    (accumStepBodyCertificate_isPolynomial
      (fun p acc y => addJet p.1 p.2 acc y) combineGroupAdd_polyTime hcprod)).1.exists_le
  obtain ⟨P, hP_pb, hcomp⟩ := groupJetSum_run_inO hJ hℓ hd hctx hcprod.2 (fun _ => 0) ct dt
    fun _ _ _ => by rw [zero_add]; exact hvt _
  exact ⟨P, hP_pb, hcomp.mono_le (fun _ => by rw [zero_add]) fun _ => le_rfl⟩

/-- Plain `ComputableInPolySpace` guarantee for `streamGroupJetSum`. -/
@[fun_prop] theorem computableInPolySpace_streamGroupJetSum {J ℓ d : ι → ℕ} {ctx : ι → α}
    {evalGroupProd : α × (ℕ × List Bool) → JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary) (hctx : ComputableInPolyTime ctx encIn encCtx)
    (hprod : ComputableInPolySpace evalGroupProd
      (encPair encCtx (encPair encUnary encBits)) encJet) :
    ComputableInPolySpace (fun x => streamGroupJetSum evalGroupProd (J x) (ℓ x) (d x) (ctx x))
      encIn encJet := by
  obtain ⟨cprod, hcprod_sp⟩ := exists_cert_of_polySpace hprod
  let cv := BooleanFold.visitCertificate (groupSumBodyCertificate cprod)
  let runAt (x : ι) (i : ℕ) := BooleanFold.runPrefix (groupSumBody evalGroupProd) (d x) i
    (((J x, ℓ x), ctx x), zeroJet (J x) (ℓ x))
  obtain ⟨P, hP_pb, hcomp⟩ := groupJetSum_run_inO hJ hℓ hd hctx hcprod_sp
    (fun x => listMax (fun i => cv.time (runAt x i)) (List.range (2 ^ d x + 1))) 0 0
    fun x j hj => by
      simpa only [Nat.zero_mul, Nat.add_zero] using le_listMax (f := fun i => cv.time (runAt x i))
        (List.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact computableInPolySpace_of_inO hP_pb hcomp

end GroupJetSum

/-! ### 3. Cross-group `r`-fold product and outer round accumulator (`streamOuterJetAccum`) -/

section OuterJetAccum

variable {ι α : Type} {encIn : ι ↪ List Bool} {encCtx : α ↪ List Bool}

/-- Add `weightedProdJet J ℓ wy.1 wy.2` into `acc` (`ℤ × List JetRows` round payload combiner). -/
def combineOuterRound (J ℓ : ℕ) (acc : JetRows) (wy : ℤ × List JetRows) : JetRows :=
  addJet J ℓ acc (weightedProdJet J ℓ wy.1 wy.2)

section Spec
variable (evalRound : α × ℕ → ℤ × List JetRows)

/-- Single-round body for `streamOuterJetAccum` (eq. (3.13) and Appendix B.2, p. 49). -/
def outerAccumBody (p : ℕ × (((ℕ × ℕ) × α) × JetRows)) : ((ℕ × ℕ) × α) × JetRows :=
  (p.2.1, combineOuterRound p.2.1.1.1 p.2.1.1.2 p.2.2 (evalRound (p.2.1.2, p.1)))

/-- Live `(J × ℓ)` jet accumulator after the first `j` outer rounds (`T_j(z, V)`). -/
def streamOuterJetAccumPrefix (J ℓ j : ℕ) (ctx : α) : JetRows :=
  (IndexFold.run (outerAccumBody evalRound) j (((J, ℓ), ctx), zeroJet J ℓ)).2.2

/-- Streaming outer round accumulator over `T_rounds` binary-indexed steps via `IndexFold.run`
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Proposition 3.4 eq. (3.13)
and Appendix B.2, pp. 49–50). -/
def streamOuterJetAccum (J ℓ T_rounds : ℕ) (ctx : α) : JetRows :=
  streamOuterJetAccumPrefix evalRound J ℓ T_rounds ctx

private theorem streamOuterJetAccumRunPrefix_snd_foldl (J ℓ j : ℕ) (ctx : α) :
    (IndexFold.run (outerAccumBody evalRound) j (((J, ℓ), ctx), zeroJet J ℓ)).2 =
      (((J, ℓ), ctx), rangeAddJet J ℓ j fun idx =>
        weightedProdJet J ℓ (evalRound (ctx, idx)).1 (evalRound (ctx, idx)).2) :=
  (IndexFold.run_accumulator (outerAccumBody evalRound) j _).trans
    (List.foldl_keep_fst (fun (par : (ℕ × ℕ) × α) acc idx =>
      combineOuterRound par.1.1 par.1.2 acc (evalRound (par.2, idx)))
      ((J, ℓ), ctx) (List.range j) (zeroJet J ℓ))
theorem streamOuterJetAccumPrefix_eq_foldl (J ℓ j : ℕ) (ctx : α) :
    streamOuterJetAccumPrefix evalRound J ℓ j ctx =
      (List.range j).foldl
        (fun acc idx =>
          addJet J ℓ acc (weightedProdJet J ℓ (evalRound (ctx, idx)).1 (evalRound (ctx, idx)).2))
        (zeroJet J ℓ) :=
  congrArg Prod.snd (streamOuterJetAccumRunPrefix_snd_foldl evalRound J ℓ j ctx)
@[simp] theorem streamOuterJetAccum_zero (J ℓ : ℕ) (ctx : α) :
    streamOuterJetAccum evalRound J ℓ 0 ctx = zeroJet J ℓ := rfl
theorem toJetTable_streamOuterJetAccumPrefix (J ℓ j : ℕ) (ctx : α) :
    toJetTable J ℓ (streamOuterJetAccumPrefix evalRound J ℓ j ctx) =
      ∑ idx ∈ Finset.range j,
        (evalRound (ctx, idx)).1 • ((evalRound (ctx, idx)).2.map (toJetTable J ℓ)).prod := by
  rw [streamOuterJetAccumPrefix_eq_foldl]; exact (toJetTable_rangeAddJet J ℓ j _).trans
    (Finset.sum_congr rfl fun idx _ => toJetTable_weightedProdJet J ℓ _ _)
theorem toJetTable_streamOuterJetAccum (J ℓ T_rounds : ℕ) (ctx : α) :
    toJetTable J ℓ (streamOuterJetAccum evalRound J ℓ T_rounds ctx) =
      ∑ idx ∈ Finset.range T_rounds,
        (evalRound (ctx, idx)).1 • ((evalRound (ctx, idx)).2.map (toJetTable J ℓ)).prod :=
  toJetTable_streamOuterJetAccumPrefix evalRound J ℓ T_rounds ctx
theorem isTableShape_streamOuterJetAccumPrefix (J ℓ j : ℕ) (ctx : α) :
    IsTableShape J ℓ (streamOuterJetAccumPrefix evalRound J ℓ j ctx) := by
  rw [streamOuterJetAccumPrefix_eq_foldl]; exact isTableShape_rangeAddJet J ℓ j _
theorem isTableShape_streamOuterJetAccum (J ℓ T_rounds : ℕ) (ctx : α) :
    IsTableShape J ℓ (streamOuterJetAccum evalRound J ℓ T_rounds ctx) :=
  isTableShape_streamOuterJetAccumPrefix evalRound J ℓ T_rounds ctx

/-- All-prefix bit-length bound for `streamOuterJetAccumPrefix` (Appendix B.2, pp. 49–50). -/
theorem length_encJetRows_streamOuterJetAccumPrefix_le {J ℓ T_rounds j M_prod : ℕ} (ctx : α)
    (hj : j ≤ T_rounds) (hM : ∀ idx < T_rounds, ∀ j' < J, ∀ u' < ℓ,
      (rowEntry (weightedProdJet J ℓ (evalRound (ctx, idx)).1 (evalRound (ctx, idx)).2)
        j' u').natAbs ≤ M_prod) :
    (encJet (streamOuterJetAccumPrefix evalRound J ℓ j ctx)).length ≤
      J * (2 * (ℓ * (2 * ((encNat T_rounds).length + M_prod.size) + 3)) + 1) := by
  have hsz : (encNat T_rounds).length = T_rounds.size := Nat.size_eq_bits_len T_rounds
  rw [streamOuterJetAccumPrefix_eq_foldl, hsz]
  exact length_encJetRows_rangeAddJet_le hj fun idx hidx => hM idx (Nat.lt_of_lt_of_le hidx hj)

end Spec

/-- Fixed-denominator `Ω = Γ ^ m` clearing for `streamOuterJetAccum` (Appendix B.2, p. 49). -/
theorem cast_streamOuterJetAccum_cleared {J ℓ r m T_rounds : ℕ} {K : Type*} [CommRing K]
    (Γ : ℤ) (evalRound : α × ℕ → ℤ × List JetRows) (ctx : α)
    (w : ℕ → ℤ) (m_group : ℕ → Fin r → ℕ)
    (H_rat : ℕ → Fin r → JetTable J ℓ K) (H_int : ℕ → Fin r → JetRows)
    (hround : ∀ idx < T_rounds, evalRound (ctx, idx) = (w idx, List.ofFn (H_int idx)))
    (hm : ∀ idx < T_rounds, ∑ g : Fin r, m_group idx g = m)
    (hH : ∀ idx < T_rounds, ∀ g : Fin r, (Γ ^ m_group idx g) • H_rat idx g =
      JetTable.castRingHom K (toJetTable J ℓ (H_int idx g))) :
    (Γ ^ m) • (∑ idx ∈ Finset.range T_rounds, w idx • ∏ g : Fin r, H_rat idx g) =
      JetTable.castRingHom K
        (toJetTable J ℓ (streamOuterJetAccum evalRound J ℓ T_rounds ctx)) := by
  rw [toJetTable_streamOuterJetAccum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun idx hidx => ?_
  have hlt := Finset.mem_range.mp hidx
  rw [hround idx hlt, map_zsmul, smul_comm (Γ ^ m) (w idx)]; congr 1; rw [← toJetTable_prodJet]
  exact cast_prodJet_ofFn_cleared Γ (m_group idx) (hm idx hlt) (H_rat idx) (H_int idx) (hH idx hlt)

/-- Direct `taylorOuterVJet` clearing for `streamOuterJetAccum` (unconditional in `K`). -/
theorem cast_streamOuterJetAccum_taylorOuterVJet {J ℓ r m T_rounds : ℕ} {K : Type*} [CommRing K]
    (Γ : ℤ) (t : K) (evalRound : α × ℕ → ℤ × List JetRows) (ctx : α)
    (w : ℕ → ℤ) (m_group : ℕ → Fin r → ℕ)
    (P_rat : ℕ → Fin r → Polynomial (Polynomial K)) (H_int : ℕ → Fin r → JetRows)
    (hround : ∀ idx < T_rounds, evalRound (ctx, idx) = (w idx, List.ofFn (H_int idx)))
    (hm : ∀ idx < T_rounds, ∑ g : Fin r, m_group idx g = m)
    (hP : ∀ idx < T_rounds, ∀ g : Fin r,
      (Γ ^ m_group idx g) • taylorOuterVJet J ℓ t (P_rat idx g) =
        JetTable.castRingHom K (toJetTable J ℓ (H_int idx g))) :
    (Γ ^ m) • taylorOuterVJet J ℓ t
        (∑ idx ∈ Finset.range T_rounds, w idx • ∏ g : Fin r, P_rat idx g) =
      JetTable.castRingHom K
        (toJetTable J ℓ (streamOuterJetAccum evalRound J ℓ T_rounds ctx)) := by
  rw [map_sum]; simp only [map_zsmul, map_prod]
  exact cast_streamOuterJetAccum_cleared Γ evalRound ctx w m_group
    (fun idx g => taylorOuterVJet J ℓ t (P_rat idx g)) H_int hround hm hP

theorem combineOuterRound_polyTime :
    ComputableInPolyTime (fun r : ((ℕ × ℕ) × JetRows) × (ℤ × List JetRows) =>
      combineOuterRound r.1.1.1 r.1.1.2 r.1.2 r.2)
      (encPair (encPair encDims encJet) encRoundOut) encJet := by unfold combineOuterRound; fun_prop

/-- Single-step `IndexFold` body certificate for `streamOuterJetAccum`. -/
noncomputable abbrev outerAccumBodyCertificate {evalRound : α × ℕ → ℤ × List JetRows}
    (cround : NativeCertificate evalRound (encPair encCtx encNat) encRoundOut) :
    NativeCertificate (outerAccumBody evalRound)
      (encPair encNat (encAccum(encCtx))) (encAccum(encCtx)) :=
  accumStepBodyCertificate (ρ := ℤ × List JetRows)
    (fun p acc wy => combineOuterRound p.1 p.2 acc wy) combineOuterRound_polyTime cround

/-- Uniform `NativeCertificate` for `streamOuterJetAccum`, built via `IndexFold.certificate`. -/
noncomputable def outerJetAccumCertificate {J ℓ T_rounds : ι → ℕ} {ctx : ι → α}
    {evalRound : α × ℕ → ℤ × List JetRows}
    (cJ : NativeCertificate J encIn encUnary) (cℓ : NativeCertificate ℓ encIn encUnary)
    (cT : NativeCertificate T_rounds encIn encNat) (cctx : NativeCertificate ctx encIn encCtx)
    (cround : NativeCertificate evalRound (encPair encCtx encNat) encRoundOut) :
    NativeCertificate (fun x => streamOuterJetAccum evalRound (J x) (ℓ x) (T_rounds x) (ctx x))
      encIn encJet :=
  NativeCertificate.snd (NativeCertificate.snd
    (IndexFold.certificate cT (initJetStateCertificate cJ cℓ cctx)
      (outerAccumBodyCertificate cround)))

/-- Explicit `ComputableInO` bound for `streamOuterJetAccum` from certificate components in time
`O((T_rounds + 1) * (R_round + P))` and space `O(P)`. -/
theorem computableInO_outerJetAccumCertificate {J ℓ T_rounds : ι → ℕ} {ctx : ι → α}
    {evalRound : α × ℕ → ℤ × List JetRows}
    (cJ : NativeCertificate J encIn encUnary) (cℓ : NativeCertificate ℓ encIn encUnary)
    (cT : NativeCertificate T_rounds encIn encNat) (cctx : NativeCertificate ctx encIn encCtx)
    (cround : NativeCertificate evalRound (encPair encCtx encNat) encRoundOut)
    (hcJ : cJ.IsPolynomial) (hcℓ : cℓ.IsPolynomial)
    (hcT : cT.IsPolynomial) (hcctx : cctx.IsPolynomial)
    (hcround_space : PolyBounded (fun q => (encPair encCtx encNat q).length) cround.space)
    (R_round : ι → ℕ)
    (hR : ∀ x idx, idx ≤ T_rounds x → cround.time (ctx x, idx) ≤ R_round x) :
    ∃ P : ι → ℕ, PolyBounded (fun x => (encIn x).length) P ∧
      ComputableInO (fun x => streamOuterJetAccum evalRound (J x) (ℓ x) (T_rounds x) (ctx x))
        encIn encJet (fun x => (T_rounds x + 1) * (R_round x + P x)) P := by
  have hwp_pt : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (ℤ × List JetRows) => weightedProdJet p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair encDims encRoundOut) encJet := by fun_prop
  have hJ_pb := (cJ.polyTime hcJ).polyBounded
  have hℓ_pb := (cℓ.polyTime hcℓ).polyBounded
  have hT_pb := (cT.polyTime hcT).polyBounded_length
  have hctx_pb := (cctx.polyTime hcctx).polyBounded_length
  obtain ⟨co, do_, hout_le⟩ := (polyBounded_length_of_hasPolySpace hcround_space).exists_le
  let inRoundLen : ι → ℕ := fun x =>
    2 * (encCtx (ctx x)).length + 1 * (encNat (T_rounds x)).length + 1
  let R_out : ι → ℕ := fun x => co * (inRoundLen x + 1) ^ do_
  have hRout_pb := NativeCertificate.polyBounded_pow_of_polyBounded
    (pb_aff 2 1 1 hctx_pb hT_pb) co do_
  obtain ⟨M_bits, hM_pb, hM_le⟩ := exists_natAbs_rowEntry_le_two_pow hwp_pt.polyBounded_length
    ((pb_aff 4 2 3 hJ_pb hℓ_pb).add hRout_pb)
  let B_acc : ι → ℕ := fun x =>
    J x * (2 * (ℓ x * (2 * ((encNat (T_rounds x)).length + (M_bits x + 1)) + 3)) + 1)
  have hBacc_pb := polyBounded_jetEncBound hJ_pb hℓ_pb hT_pb (hM_pb.add (.const 1))
  let B_state : ι → ℕ := fun x =>
    (8 * J x + 4 * ℓ x + 0) + (2 * (encCtx (ctx x)).length + 1 * B_acc x + 7)
  have hBstate_pb := (pb_aff 8 4 0 hJ_pb hℓ_pb).add (pb_aff 2 1 7 hctx_pb hBacc_pb)
  let runO (x : ι) (j : ℕ) := IndexFold.run (outerAccumBody evalRound) j
    (((J x, ℓ x), ctx x), zeroJet (J x) (ℓ x))
  have hB : ∀ x j, j ≤ T_rounds x → (encAccum(encCtx) (runO x j).2).length ≤ B_state x :=
    fun x j hj => by
      have hdims : (encDims (J x, ℓ x)).length = 2 * J x + 1 + ℓ x := by
        simp only [length_encPair, encUnary_apply, List.length_replicate]
      have hacc_len : (encJet (streamOuterJetAccumPrefix evalRound (J x) (ℓ x) j (ctx x))).length ≤
          B_acc x := by
        have h := length_encJetRows_streamOuterJetAccumPrefix_le evalRound
          (J := J x) (ℓ := ℓ x) (M_prod := 2 ^ M_bits x) (ctx x) hj fun idx hlt j' _ u' _ =>
            hM_le x ((J x, ℓ x), evalRound (ctx x, idx)) (by
              have hrin : (encPair encCtx encNat (ctx x, idx)).length ≤ inRoundLen x := by
                have := length_encNat_mono hlt.le
                dsimp only [inRoundLen]; simp only [length_encPair]; omega
              have hr := (hout_le (ctx x, idx)).trans
                (Nat.mul_le_mul_left co (Nat.pow_le_pow_left (Nat.add_le_add_right hrin 1) do_))
              dsimp only [inRoundLen] at hr; simp only [length_encPair] at hr
              simp only [length_encPair, hdims]; omega) j' u'
        rwa [Nat.size_pow] at h
      have hf := congrArg Prod.fst
        (streamOuterJetAccumRunPrefix_snd_foldl evalRound (J x) (ℓ x) j (ctx x))
      have hpar : (runO x j).2 =
          (((J x, ℓ x), ctx x), streamOuterJetAccumPrefix evalRound (J x) (ℓ x) j (ctx x)) :=
        Prod.ext hf rfl
      rw [hpar]; dsimp only [B_state, B_acc] at hacc_len ⊢
      simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
  let S_st : ι → ℕ := fun x => 2 * (encNat (T_rounds x)).length + 1 + B_state x
  have hSst_pb := (((PolyBounded.const 2).mul hT_pb).add (.const 1)).add hBstate_pb
  obtain ⟨c_b, d_b, hbody_t⟩ := exists_accumStepBodyCertificate_time_le
    (fun p acc wy => combineOuterRound p.1 p.2 acc wy) combineOuterRound_polyTime hcround_space
  obtain ⟨P, hP_pb, hcomp⟩ := computableInO_snd_indexFold cT
    (initJetStateCertificate cJ cℓ cctx) (outerAccumBodyCertificate cround) hcT
    (initJetStateCertificate_isPolynomial hcJ hcℓ hcctx)
    (hasPolySpace_accumStepBodyCertificate
      (fun p acc wy => combineOuterRound p.1 p.2 acc wy) combineOuterRound_polyTime hcround_space)
    hBstate_pb hB R_round (fun x => c_b * (S_st x + 1) ^ d_b)
    (NativeCertificate.polyBounded_pow_of_polyBounded hSst_pb c_b d_b) fun x j hj hst_len => by
      have hidx : (runO x j).1 = j := IndexFold.run_index _ _ _
      have hpar : (runO x j).2.1 = ((J x, ℓ x), ctx x) :=
        congrArg Prod.fst (streamOuterJetAccumRunPrefix_snd_foldl evalRound (J x) (ℓ x) j (ctx x))
      have hb := hbody_t (runO x j); rw [hpar, hidx] at hb
      exact hb.trans (Nat.add_le_add (hR x j hj)
        (Nat.mul_le_mul_left c_b (Nat.pow_le_pow_left (Nat.add_le_add_right hst_len 1) d_b)))
  exact ⟨P, hP_pb, (NativeCertificate.snd (⟨_, _, hcomp⟩ : NativeCertificate _ encIn _)).computes⟩

/-- Explicit `(T_rounds + 1) * P` `ComputableInO` bound for `streamOuterJetAccum` when `evalRound`
is computable in polynomial time. -/
theorem computableInO_streamOuterJetAccum {J ℓ T_rounds : ι → ℕ} {ctx : ι → α}
    {evalRound : α × ℕ → ℤ × List JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hT : ComputableInPolyTime T_rounds encIn encNat) (hctx : ComputableInPolyTime ctx encIn encCtx)
    (hround : ComputableInPolyTime evalRound (encPair encCtx encNat) encRoundOut) :
    ∃ P : ι → ℕ, PolyBounded (fun x => (encIn x).length) P ∧
      ComputableInO (fun x => streamOuterJetAccum evalRound (J x) (ℓ x) (T_rounds x) (ctx x))
        encIn encJet (fun x => (T_rounds x + 1) * P x) P := by
  have hcround := NativeCertificate.ofPolyTime_isPolynomial hround
  obtain ⟨ct, dt, ht_le⟩ := hcround.1.exists_le
  let inRoundLen : ι → ℕ := fun x =>
    2 * (encCtx (ctx x)).length + 1 * (encNat (T_rounds x)).length + 1
  have hinRound_pb := pb_aff 2 1 1 hctx.polyBounded_length hT.polyBounded_length
  let R_round : ι → ℕ := fun x => ct * (inRoundLen x + 1) ^ dt
  have hR_pb := NativeCertificate.polyBounded_pow_of_polyBounded hinRound_pb ct dt
  obtain ⟨P, hP_pb, hcomp⟩ := computableInO_outerJetAccumCertificate
    (.ofPolyTime hJ) (.ofPolyTime hℓ) (.ofPolyTime hT) (.ofPolyTime hctx) (.ofPolyTime hround)
    (NativeCertificate.ofPolyTime_isPolynomial hJ) (NativeCertificate.ofPolyTime_isPolynomial hℓ)
    (NativeCertificate.ofPolyTime_isPolynomial hT) (NativeCertificate.ofPolyTime_isPolynomial hctx)
    hcround.2 R_round fun x idx hidx => by
      have hrin : (encPair encCtx encNat (ctx x, idx)).length ≤ inRoundLen x := by
        have := length_encNat_mono hidx
        dsimp only [inRoundLen]; simp only [length_encPair]; omega
      exact (ht_le (ctx x, idx)).trans
        (Nat.mul_le_mul_left ct (Nat.pow_le_pow_left (Nat.add_le_add_right hrin 1) dt))
  exact ⟨fun x => R_round x + P x, hR_pb.add hP_pb,
    hcomp.mono_le (fun _ => le_rfl) fun _ => Nat.le_add_left _ _⟩

/-- Plain `ComputableInPolySpace` guarantee for `streamOuterJetAccum` when `evalRound` is
computable in polynomial space. -/
@[fun_prop] theorem computableInPolySpace_streamOuterJetAccum {J ℓ T_rounds : ι → ℕ} {ctx : ι → α}
    {evalRound : α × ℕ → ℤ × List JetRows}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hT : ComputableInPolyTime T_rounds encIn encNat) (hctx : ComputableInPolyTime ctx encIn encCtx)
    (hround : ComputableInPolySpace evalRound (encPair encCtx encNat) encRoundOut) :
    ComputableInPolySpace (fun x => streamOuterJetAccum evalRound (J x) (ℓ x) (T_rounds x) (ctx x))
      encIn encJet := by
  obtain ⟨cround, hcround_space⟩ := exists_cert_of_polySpace hround
  obtain ⟨P, hP_pb, hcomp⟩ := computableInO_outerJetAccumCertificate
    (.ofPolyTime hJ) (.ofPolyTime hℓ) (.ofPolyTime hT) (.ofPolyTime hctx) cround
    (NativeCertificate.ofPolyTime_isPolynomial hJ) (NativeCertificate.ofPolyTime_isPolynomial hℓ)
    (NativeCertificate.ofPolyTime_isPolynomial hT) (NativeCertificate.ofPolyTime_isPolynomial hctx)
    hcround_space (fun x => listMax (fun i => cround.time (ctx x, i)) (List.range (T_rounds x + 1)))
    fun x idx hidx => le_listMax (f := fun i => cround.time (ctx x, i))
      (List.mem_range.mpr (Nat.lt_succ_of_le hidx))
  exact computableInPolySpace_of_inO hP_pb hcomp

end OuterJetAccum

/-! ### 4. Confluent Hermite Cramer recovery from per-node outer jets -/

section HermiteRecovery

/-- Recover `(∑_{u < ℓ} H_u(0)).modPowTwo ℓ` from per-node `J × ℓ` `Ω`-scaled Taylor-jet arrays
`nodeJets` at `nodes` via `extractAllCoordNodeJets` and `Cslib.Circuits.Rational.hermiteRecoverZero`
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], eq. (5.5) and Appendix B.3,
p. 50; returns `0` when `ℓ = 0`, `Ω = 0`, or `detRows (hermiteRows nodes J) = 0`). -/
def recoverOuterJetSumModPowTwo (nodes : List ℤ) (J ℓ : ℕ) (Ω : ℤ) (nodeJets : List JetRows) : ℤ :=
  (((extractAllCoordNodeJets J ℓ nodeJets).map
    (Cslib.Circuits.Rational.hermiteRecoverZero nodes J Ω)).sum).modPowTwo ℓ

@[simp] theorem recoverOuterJetSumModPowTwo_zero_cols (nodes : List ℤ) (J : ℕ) (Ω : ℤ)
    (nodeJets : List JetRows) : recoverOuterJetSumModPowTwo nodes J 0 Ω nodeJets = 0 := rfl

/-- Single-coordinate confluent Hermite Cramer recovery of `(P.coeff u).eval 0 = H_zero`. -/
theorem hermiteRecoverZero_extractCoordNodeJets_eq {J ℓ : ℕ} {Ω H_zero : ℤ} {nodes : List ℤ}
    (hnodup : nodes.Nodup) (hΩ : Ω ≠ 0) (nodeJets : List JetRows)
    (hlen : nodeJets.length = nodes.length) (P : Polynomial (Polynomial ℚ))
    (hclear : ∀ i : Fin nodes.length, Ω • taylorOuterVJet J ℓ (nodes[i] : ℚ) P =
      JetTable.castRingHom ℚ (toJetTable J ℓ (nodeJets[i.1]'(hlen.symm ▸ i.isLt))))
    (u : Fin ℓ) (hdeg : (P.coeff u).natDegree < nodes.length * J)
    (hH0 : (P.coeff u).eval 0 = (H_zero : ℚ)) :
    Cslib.Circuits.Rational.hermiteRecoverZero nodes J Ω (extractCoordNodeJets J u nodeJets) =
      H_zero := by
  have hshape := isTableShape_extractCoordNodeJets J u nodeJets
  exact Cslib.Circuits.Rational.hermiteRecoverZero_eq_of_rowEntry hnodup hΩ hdeg hH0
    (hshape.1.trans hlen) hshape.2
    (rowEntry_extractCoordNodeJets_eq_taylor Ω nodes nodeJets hlen P hclear u)

/-- Full multi-coordinate modular count recovery `S_ℓ(H(0)) ≡ count (mod 2 ^ ℓ)` from `Ω`-scaled
per-node outer Taylor jets ([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH],
eq. (5.5) and Appendix B.3, p. 50). -/
theorem recoverOuterJetSumModPowTwo_eq {J ℓ : ℕ} {Ω count : ℤ} {nodes : List ℤ}
    (hnodup : nodes.Nodup) (hΩ : Ω ≠ 0) (nodeJets : List JetRows)
    (hlen : nodeJets.length = nodes.length) (P : Polynomial (Polynomial ℚ)) (H_zero : Fin ℓ → ℤ)
    (hclear : ∀ i : Fin nodes.length, Ω • taylorOuterVJet J ℓ (nodes[i] : ℚ) P =
      JetTable.castRingHom ℚ (toJetTable J ℓ (nodeJets[i.1]'(hlen.symm ▸ i.isLt))))
    (hdeg : ∀ u : Fin ℓ, (P.coeff u).natDegree < nodes.length * J)
    (hH0 : ∀ u : Fin ℓ, (P.coeff u).eval 0 = (H_zero u : ℚ))
    (hcount₀ : 0 ≤ count) (hcount₁ : count < (2 : ℤ) ^ ℓ)
    (hdvd : (2 : ℤ) ^ ℓ ∣ (∑ u : Fin ℓ, H_zero u) - count) :
    recoverOuterJetSumModPowTwo nodes J ℓ Ω nodeJets = count := by
  have hsum : ((extractAllCoordNodeJets J ℓ nodeJets).map
      (Cslib.Circuits.Rational.hermiteRecoverZero nodes J Ω)).sum = ∑ u : Fin ℓ, H_zero u := by
    rw [extractAllCoordNodeJets, List.map_map, Function.comp_def, List.sum_map_range]
    exact Finset.sum_congr rfl fun u _ =>
      hermiteRecoverZero_extractCoordNodeJets_eq hnodup hΩ nodeJets hlen P hclear u (hdeg u) (hH0 u)
  rw [recoverOuterJetSumModPowTwo, hsum]; exact Int.modPowTwo_eq_of_dvd_sub hcount₀ hcount₁ hdvd

/-- Outer-round accumulation plus Cramer count recovery from supplied cleared group payloads across
`Q` distinct `nodes`. -/
theorem recoverOuterJetSumModPowTwo_streamOuterJetAccum_eq {α : Type} {J ℓ r m T_rounds : ℕ}
    {Γ count : ℤ} {nodes : List ℤ} (hnodup : nodes.Nodup) (hΓ : Γ ≠ 0)
    (evalRound : α × ℕ → ℤ × List JetRows) (nodeCtx : Fin nodes.length → α)
    (w : ℕ → ℤ) (m_group : ℕ → Fin r → ℕ) (P_rat : ℕ → Fin r → Polynomial (Polynomial ℚ))
    (H_int : Fin nodes.length → ℕ → Fin r → JetRows) (H_zero : Fin ℓ → ℤ)
    (hround : ∀ i idx, idx < T_rounds →
      evalRound (nodeCtx i, idx) = (w idx, List.ofFn (H_int i idx)))
    (hm : ∀ idx < T_rounds, ∑ g : Fin r, m_group idx g = m)
    (hP : ∀ (i : Fin nodes.length) idx, idx < T_rounds → ∀ g : Fin r,
      (Γ ^ m_group idx g) • taylorOuterVJet J ℓ (nodes[i] : ℚ) (P_rat idx g) =
        JetTable.castRingHom ℚ (toJetTable J ℓ (H_int i idx g)))
    (hdeg : ∀ u : Fin ℓ, ((∑ idx ∈ Finset.range T_rounds, w idx • ∏ g : Fin r, P_rat idx g).coeff
      u).natDegree < nodes.length * J)
    (hH0 : ∀ u : Fin ℓ, ((∑ idx ∈ Finset.range T_rounds, w idx • ∏ g : Fin r, P_rat idx g).coeff
      u).eval 0 = (H_zero u : ℚ))
    (hcount₀ : 0 ≤ count) (hcount₁ : count < (2 : ℤ) ^ ℓ)
    (hdvd : (2 : ℤ) ^ ℓ ∣ (∑ u : Fin ℓ, H_zero u) - count) :
    recoverOuterJetSumModPowTwo nodes J ℓ (Γ ^ m)
      (List.ofFn fun i => streamOuterJetAccum evalRound J ℓ T_rounds (nodeCtx i)) = count := by
  refine recoverOuterJetSumModPowTwo_eq hnodup (pow_ne_zero m hΓ) _ (List.length_ofFn)
    (∑ idx ∈ Finset.range T_rounds, w idx • ∏ g : Fin r, P_rat idx g) H_zero (fun i => ?_)
    hdeg hH0 hcount₀ hcount₁ hdvd
  simpa only [List.getElem_ofFn] using cast_streamOuterJetAccum_taylorOuterVJet Γ (nodes[i] : ℚ)
    evalRound (nodeCtx i) w m_group P_rat (H_int i) (hround i) hm (hP i)

@[fun_prop] theorem computableInPolyTime_recoverOuterJetSumModPowTwo {α : Type}
    {encIn : α ↪ List Bool} {nodes : α → List ℤ} {J ℓ : α → ℕ} {Ω : α → ℤ}
    {nodeJets : α → List JetRows} (hnodes : ComputableInPolyTime nodes encIn (encList encIntBin))
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hΩ : ComputableInPolyTime Ω encIn encIntBin)
    (hnodeJets : ComputableInPolyTime nodeJets encIn encJets) :
    ComputableInPolyTime
      (fun x => recoverOuterJetSumModPowTwo (nodes x) (J x) (ℓ x) (Ω x) (nodeJets x))
      encIn encIntBin := by unfold recoverOuterJetSumModPowTwo; fun_prop

end HermiteRecovery

end Cslib.CommonCountingAccum
