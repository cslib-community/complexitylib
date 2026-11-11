/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.AffineDisperser.Li.PolyTime
import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.SomewhereCondenser
import Mathlib.Tactic.NormNum.Prime

/-!
# Clients for Li's affine disperser base layer and Shoup `O(N ^ (4 / 5))` disperser

Exercises the combinatoric affine-source and somewhere-condenser layers
(`CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.AffineSource` and
`SomewhereCondenser`), deterministic Berlekamp and Shoup irreducible polynomial construction
(`Berlekamp`, `ShoupIrreducible`, `ShoupPolyTime`), the polynomial-time explicit `O(N ^ (4 / 5))`
disperser `primeDisperserLanguage`, its `3.5 N - 15036 N ^ (4 / 5)` Boolean circuit size lower
bound over `B₂`, and clean standard-axiom dependencies.
-/

namespace CslibFrontierTests.LiAffineDisperser

open Cslib Cslib.AffineDisperser Cslib.AffineDisperser.Li Cslib.AffineDisperser.Explicit
open Cslib.Circuits Turing.MultiTapeTM

/-! ### Combinatoric affine sources and somewhere condensers -/

/-- The uniform distribution on the full `2`-bit cube `(⊤ : AffineSubspace Bool (BitString 2))`
is a `(2, 2)`-affine source and hence has min-entropy `2`. -/
example :
    let X := uniformAffine (⊤ : AffineSubspace Bool (BitString 2)) ⟨0, Set.mem_univ _⟩
    IsAffineSource X 2 ∧ Cslib.Probability.PMF.minEntropy X = (2 : ℝ) := by
  intro X
  have hX : IsAffineSource X 2 := by
    refine ⟨⊤, ⟨0, Set.mem_univ _⟩, ?_, rfl⟩
    rw [AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  have hmin := minEntropy_of_isAffineSource hX
  norm_num at hmin
  exact ⟨hX, hmin⟩

/-- Three explicit linear maps on `BitString 2`: identity, coordinate swap, and triangular shear. -/
noncomputable def dimExpander2 : Fin 3 → BitString 2 →ₗ[Bool] BitString 2
  | ⟨0, _⟩ => LinearMap.id
  | ⟨1, _⟩ =>
      { toFun := fun x i => if i.1 = 0 then x 1 else x 0
        map_add' := fun x y => by funext i; fin_cases i <;> rfl
        map_smul' := fun c x => by funext i; fin_cases i <;> rfl }
  | ⟨2, _⟩ =>
      { toFun := fun x i => if i.1 = 0 then x 0 else x 0 + x 1
        map_add' := fun x y => by
          funext i
          fin_cases i
          · rfl
          · change (x 0 + y 0) + (x 1 + y 1) = (x 0 + x 1) + (y 0 + y 1)
            ring
        map_smul' := fun c x => by
          funext i
          fin_cases i
          · rfl
          · change c * x 0 + c * x 1 = c * (x 0 + x 1)
            ring }

/-- Basis vectors `e0 = (true, false)` and `e1 = (false, true)` in `BitString 2`. -/
private abbrev e0 : BitString 2 := fun i => i == 0
private abbrev e1 : BitString 2 := fun i => i == 1

/-- `dimExpander2` is a `1`-dimension expander on `BitString 2`, so `basicCond dimExpander2`
is a non-trivial `(1 / 2, 13 / 24)` affine somewhere condenser. -/
theorem isAffineSomewhereCondenser_dimExpander2 :
    IsAffineSomewhereCondenser (basicCond dimExpander2) (1 / 2 : ℝ) (13 / 24 : ℝ) := by
  have hexp : IsDimensionExpander dimExpander2 1 := by
    intro V hV
    rcases Nat.eq_zero_or_pos (Module.finrank Bool V) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, mul_zero, Nat.cast_nonneg]
    · have hV_ne : V ≠ ⊥ := by
        rintro rfl
        rw [finrank_bot] at hpos
        exact Nat.lt_irrefl 0 hpos
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV_ne
      set S := ⨆ i, V.map (dimExpander2 i)
      have h0mem : dimExpander2 0 v ∈ S := Submodule.mem_iSup_of_mem 0 ⟨v, hv, rfl⟩
      have h1mem : dimExpander2 1 v ∈ S := Submodule.mem_iSup_of_mem 1 ⟨v, hv, rfl⟩
      have h2mem : dimExpander2 2 v ∈ S := Submodule.mem_iSup_of_mem 2 ⟨v, hv, rfl⟩
      have hv_ne : v 0 ≠ false ∨ v 1 ≠ false := by
        by_contra h
        push Not at h
        apply hv0
        funext i
        fin_cases i <;> [exact h.1; exact h.2]
      have htop : S = ⊤ := by
        have hbasis : e0 ∈ S ∧ e1 ∈ S := by
          cases hb0 : v 0 <;> cases hb1 : v 1
          · exact absurd ⟨hb0, hb1⟩ (not_and_or.mpr hv_ne)
          · refine ⟨?_, ?_⟩
            · convert h1mem using 1
              funext i; fin_cases i <;> simp [dimExpander2, e0, hb0, hb1]
            · convert h0mem using 1
              funext i; fin_cases i <;> simp [dimExpander2, e1, hb0, hb1]
          · refine ⟨?_, ?_⟩
            · convert h0mem using 1
              funext i; fin_cases i <;> simp [dimExpander2, e0, hb0, hb1]
            · convert h1mem using 1
              funext i; fin_cases i <;> simp [dimExpander2, e1, hb0, hb1]
          · have he0 : e0 ∈ S := by
              convert h2mem using 1
              funext i
              fin_cases i
              · change e0 0 = v 0
                rw [hb0]; rfl
              · change e0 1 = v 0 + v 1
                rw [hb0, hb1]; decide
            refine ⟨he0, ?_⟩
            have hadd := S.add_mem h0mem he0
            convert hadd using 1
            funext i
            fin_cases i
            · change e1 0 = v 0 + e0 0
              rw [hb0]; decide
            · change e1 1 = v 1 + e0 1
              rw [hb1]; decide
        rw [eq_top_iff]
        intro w _
        have hw : w = (if w 0 = true then e0 else 0) + (if w 1 = true then e1 else 0) := by
          funext i
          cases h0 : w 0 <;> cases h1 : w 1 <;> fin_cases i <;>
            simp only [Fin.zero_eta, Fin.mk_one, Pi.add_apply, Pi.zero_apply, e0, e1, h0, h1,
              Bool.false_eq_true, ↓reduceIte] <;>
            decide
        rw [hw]
        refine S.add_mem ?_ ?_ <;> split_ifs <;> [exact hbasis.1; exact S.zero_mem;
          exact hbasis.2; exact S.zero_mem]
      rw [htop, finrank_top, Module.finrank_fin_fun]
      norm_num
      have hV1 : Module.finrank Bool V ≤ 1 := by omega
      exact_mod_cast hV1
  have hcond := isAffineSomewhereCondenser_basicCond (d := 3) (by decide)
    (α := 1) (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hexp
  norm_num at hcond
  exact hcond

/-! ### Deterministic Berlekamp and Shoup irreducible polynomials -/

example :
    polyTrim [true, false, true, false, false] = [true, false, true] ∧
      polyGcd [true, false, false, true] [true, true, true] = [true, true, true] := by
  decide

/-- `shoupIrreducibleBits 3` and `shoupIrreducibleBits 5` produce genuine irreducible binary
polynomials of exact degrees `3` and `5`. -/
example :
    Irreducible (polyOfBits (shoupIrreducibleBits 3)) ∧
      (polyOfBits (shoupIrreducibleBits 3)).natDegree = 3 ∧
      Irreducible (polyOfBits (shoupIrreducibleBits 5)) ∧
      (polyOfBits (shoupIrreducibleBits 5)).natDegree = 5 :=
  ⟨irreducible_polyOfBits_shoupIrreducibleBits (by norm_num) (by norm_num),
    natDegree_polyOfBits_shoupIrreducibleBits (by norm_num) (by norm_num),
    irreducible_polyOfBits_shoupIrreducibleBits (by norm_num) (by norm_num),
    natDegree_polyOfBits_shoupIrreducibleBits (by norm_num) (by norm_num)⟩

/-- Pseudorandom bits from an LCG, exercising `primeDisperserBits` at `N = 64`. -/
def lcgBits (N seed : ℕ) : List Bool :=
  ((List.range N).foldl (fun (state : ℕ × List Bool) _ =>
    let s := (state.1 * 1103515245 + 12345) % 2 ^ 31
    (s, state.2 ++ [s / 2 ^ 16 % 2 == 1])) (seed, [])).2

/-- info: ([true, true, false, true], [true, false, true, false, false, true], 11, false, true) -/
#guard_msgs in
#eval (shoupIrreducibleBits 3, shoupIrreducibleBits 5, primeDeg 64,
  primeDisperserBits 64 (lcgBits 64 1), primeDisperserBits 64 (lcgBits 64 3))

/-! ### Threshold bound, polynomial-time disperser, and `B₂` circuit lower bound -/

/-- Exact evaluation of `fifthRoot` on `242` and `243` via `fifthRoot_spec`. -/
example : fifthRoot 242 = 2 ∧ fifthRoot 243 = 3 := by
  have h242 := fifthRoot_spec 242
  have h243 := fifthRoot_spec 243
  refine ⟨?_, ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (fifthRoot 242 + 1) ^ 5 ≤ 2 ^ 5 := Nat.pow_le_pow_left (by omega) 5
      omega
    · have : 3 ^ 5 ≤ (fifthRoot 242) ^ 5 := Nat.pow_le_pow_left (by omega) 5
      omega
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (fifthRoot 243 + 1) ^ 5 ≤ 3 ^ 5 := Nat.pow_le_pow_left (by omega) 5
      omega
    · have : 4 ^ 5 ≤ (fifthRoot 243) ^ 5 := Nat.pow_le_pow_left (by omega) 5
      omega

/-- At `N = 2 ^ 75`, `fifthRoot N = 2 ^ 15 = 32768`, and `14 * (primeThreshold N + 1) < N`
without kernel-evaluating `primeDeg (2 ^ 75)`. -/
theorem fourteen_mul_primeThreshold_two_pow_75_lt :
    14 * (primeThreshold (2 ^ 75) + 1) < 2 ^ 75 := by
  set N := 2 ^ 75
  have h5 : fifthRoot N = 2 ^ 15 := by
    have hspec := fifthRoot_spec N
    have hpow : (2 ^ 15) ^ 5 = N := by norm_num [N]
    have h1 : fifthRoot N ≤ 2 ^ 15 := by
      by_contra hgt
      have : 2 ^ 15 + 1 ≤ fifthRoot N := by omega
      have : N < (fifthRoot N) ^ 5 := by
        calc N = (2 ^ 15) ^ 5 := hpow.symm
          _ < (2 ^ 15 + 1) ^ 5 := Nat.pow_lt_pow_left (by omega) (by norm_num)
          _ ≤ (fifthRoot N) ^ 5 := Nat.pow_le_pow_left this 5
      omega
    have h2 : 2 ^ 15 ≤ fifthRoot N := by
      by_contra hlt
      have : fifthRoot N + 1 ≤ 2 ^ 15 := by omega
      have : (fifthRoot N + 1) ^ 5 ≤ N := by
        calc (fifthRoot N + 1) ^ 5 ≤ (2 ^ 15) ^ 5 := Nat.pow_le_pow_left this 5
          _ = N := hpow
      omega
    omega
  obtain ⟨_, hq_low, hq_high⟩ := primeDeg_spec N
  have hbound : primeThresholdBound N = (2 ^ 15) ^ 3 := by
    change (max 2 (fifthRoot N)) ^ 3 = (2 ^ 15) ^ 3
    rw [h5, max_eq_right (by norm_num)]
  rw [hbound] at hq_low hq_high
  have hsym : primeSymDeg N = 2 ^ 15 := by
    change max 1 (fifthRoot N) = 2 ^ 15
    rw [h5, max_eq_right (by norm_num)]
  set q := primeDeg N
  set r := N / q
  have hr_ub : r ≤ 2 ^ 30 := by
    refine Nat.div_le_of_le_mul ?_
    calc N = (2 ^ 15) ^ 3 * 2 ^ 30 := by norm_num [N]
      _ ≤ q * 2 ^ 30 := Nat.mul_le_mul_right _ (by omega)
  have hr1 : r * (r + 1) ≤ 2 ^ 30 * (2 ^ 30 + 1) := Nat.mul_le_mul hr_ub (by omega)
  have hqt : q * 2 ^ 15 ≤ 2 * (2 ^ 15) ^ 3 * 2 ^ 15 := Nat.mul_le_mul_right _ hq_high
  have hwaste : N - r * q < q := by
    have hdiv := Nat.div_add_mod N q
    change q * r + N % q = N at hdiv
    have hmod := Nat.mod_lt N (by omega : 0 < q)
    rw [mul_comm r q]
    omega
  have hqr_N : q * r ≤ N := Nat.mul_div_le N q
  have hqr_div : q * r / primeSymDeg N ≤ 2 ^ 60 := by
    rw [hsym]
    refine Nat.div_le_of_le_mul ?_
    calc q * r ≤ N := hqr_N
      _ = 2 ^ 15 * 2 ^ 60 := by norm_num [N]
  change 14 * ((N - r * q) + (r * (r + 1) + r * (r + 1) + q * primeSymDeg N +
      q * r / primeSymDeg N) + 1) < N
  rw [hsym]
  omega

/-- Non-vacuous disperser separation at `N = 2 ^ 75`: `primeDisperser (2 ^ 75)` is nonconstant
on the `BitString (primeThreshold (2 ^ 75) + 1)` zero-extension subspace. -/
theorem exists_primeDisperser_zeroExtend_ne :
    ∃ x y : BitString (primeThreshold (2 ^ 75) + 1),
      primeDisperser (2 ^ 75) (BitString.zeroExtend x) ≠
        primeDisperser (2 ^ 75) (BitString.zeroExtend y) :=
  isAffineDisperser_primeDisperser (2 ^ 75) _ BitString.isAffine_zeroExtend
    (BitString.zeroExtend_injective (by
      have := fourteen_mul_primeThreshold_two_pow_75_lt
      omega))

/-- Concrete `> 3 * 2 ^ 75` gate lower bound over `B₂` for `primeDisperser (2 ^ 75)`,
accompanied by an actual `B₂` circuit computing it (non-vacuous). -/
example :
    ∃ C : Circuit (fullSignature 2 Bool) (2 ^ 75) 1,
      C.Computes fullInterpretation (single (primeDisperser (2 ^ 75))) ∧
        3 * 2 ^ 75 < C.size := by
  obtain ⟨C, hC⟩ := Interpretation.IsComplete.exists_computes_single
    (I := fullInterpretation (k := 2) (Carrier := Bool)) (primeDisperser (2 ^ 75))
  have h7 := seven_mul_le_two_mul_size_add_primeThreshold C hC
  have h14 := fourteen_mul_primeThreshold_two_pow_75_lt
  exact ⟨C, hC, by omega⟩

/-- Headline `P` membership and asymptotic `3.5 N - O(N ^ (4 / 5))` `B₂` lower bound. -/
example :
    (∀ N, primeDisperserLanguage.slice N = primeDisperser N) ∧
      (primeDisperserLanguage : Set (List Bool)) ∈ Complexity.P encBits ∧
      (∀ᶠ N in Filter.atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (primeDisperserLanguage.slice N)) →
          (7 : ℝ) / 2 * (N : ℝ) - 15036 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.size : ℝ)) ∧
      ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.P encBits ∧
        ∀ᶠ N in Filter.atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
          C.Computes fullInterpretation (single (L.slice N)) →
            (7 : ℝ) / 2 * (N : ℝ) - 15036 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.size : ℝ) :=
  ⟨slice_primeDisperserLanguage, primeDisperserLanguage_mem_P,
    by simpa only [slice_primeDisperserLanguage] using
      eventually_le_size_of_computes_primeDisperser,
    exists_mem_P_eventually_le_size_primeDisperser⟩

/-- info: 'Cslib.AffineDisperser.Li.isAffineSomewhereCondenser_sCond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.AffineDisperser.Li.isAffineSomewhereCondenser_sCond

/-- info: 'Cslib.AffineDisperser.Li.shoupIrreducibleBits_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.AffineDisperser.Li.shoupIrreducibleBits_spec

/-- info: 'Cslib.AffineDisperser.Li.isAffineDisperser_primeDisperser' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.AffineDisperser.Li.isAffineDisperser_primeDisperser

/--
info: 'Cslib.AffineDisperser.Li.exists_mem_P_eventually_le_size_primeDisperser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.AffineDisperser.Li.exists_mem_P_eventually_le_size_primeDisperser

end CslibFrontierTests.LiAffineDisperser
