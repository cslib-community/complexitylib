/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof
public import CslibFrontier.Computability.Circuit.Boolean.Razborov.RankProperty
import CslibFrontier.Computability.Circuit.Boolean.GF2Rank

/-!
# The rank property is `P/poly`-natural

The rank test of `Cslib.Circuits.Boolean.Razborov.rankTest` is decided from truth tables by De
Morgan circuits of size `173 · 8 ^ n`, cubic in the length `2 ^ n` of the truth table. Each entry
of the zero-sum matrix is an exclusive or of truth-table bits
(`Cslib.Circuits.Boolean.Razborov.zeroSumMatrix_apply`), and the circuits of
`Cslib.Circuits.Boolean.synthesis_le_rank_of_synthesis` compare its rank over `ZMod 2` with
`C(n, a) / 2`. So along any level function `a`, the rank property has its truth-table language in
`P/poly`. With the largeness of the rank test, the rank property is `P/poly`-natural.

The size bound is this library's, not a source's. The circuits chain one Gauss–Jordan stage per
column; their depth is not certified here.

This is the constructive and large half of a natural proof. Usefulness against `AC⁰[2]` along the
middle level is `Cslib.Circuits.Boolean.Razborov.isUseful_AC0Mod_two_rankProperty`, in
`CslibFrontier.Computability.Circuit.Boolean.Razborov.Useful`.

## Main definitions

* `Cslib.Circuits.Boolean.Razborov.rankProperty a`: the rank test at level `a n` on `n` inputs
  (`rankProperty_apply`).

## Main results

* `Cslib.Circuits.Boolean.Razborov.synthesis_truthTableTest_rankTest`: the rank test from truth
  tables within `173 · 8 ^ n` gates.
* `Cslib.Circuits.Boolean.Razborov.truthTableLanguage_rankProperty_mem_PPoly`: constructivity.
* `Cslib.Circuits.Boolean.Razborov.isLarge_rankProperty`: largeness.
* `Cslib.Circuits.Boolean.Razborov.isNatural_PPoly_rankProperty`: the rank property is
  `P/poly`-natural.

## References

[Razborov and Rudich, §3.2, p. 27][RazborovRudich1997] state the rank property abstractly and
observe that rank over GF(2) is in NC², which gives constructivity; they give no explicit circuit
or gate count. The test here is the variant of `Cslib.Circuits.Boolean.Razborov.rankTest`, with one
square matrix and the threshold `C(n, a) / 2`.
-/

public section

namespace Cslib.Circuits.Boolean.Razborov

open Finset Matrix BitString MCSP NaturalProof Filter

variable {n : ℕ}

/-! ### The zero-sum matrix of a truth table -/

/-- The `a`-subsets of `Fin n`, numbered. -/
private noncomputable def subsetEquiv (n a : ℕ) :
    {I : Finset (Fin n) // #I = a} ≃ Fin (n.choose a) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_finset_len, Fintype.card_fin])

/-- The zero-sum matrix of the function with truth table `T`, with numbered rows and columns. -/
private noncomputable def truthTableMatrix (n a : ℕ) (T : BitString (2 ^ n)) :
    Matrix (Fin (n.choose a)) (Fin (n.choose a)) (ZMod 2) :=
  (zeroSumMatrix a fun x => bitVal (ZMod 2) ((truthTable n).symm T x)).reindex
    (subsetEquiv n a) (subsetEquiv n a)

private theorem rank_truthTableMatrix (n a : ℕ) (T : BitString (2 ^ n)) :
    (truthTableMatrix n a T).rank =
      (zeroSumMatrix a fun x => bitVal (ZMod 2) ((truthTable n).symm T x)).rank :=
  rank_reindex _ _ _

/-- An entry of the matrix is an exclusive or of truth-table bits. -/
private theorem bitEquiv_truthTableMatrix (n a : ℕ) (T : BitString (2 ^ n))
    (i j : Fin (n.choose a)) :
    bitEquiv (truthTableMatrix n a T i j) =
      ∑ x with ∀ k ∈ ((subsetEquiv n a).symm i).1 ∪ ((subsetEquiv n a).symm j).1, x k = false,
        T (BitString.equivFin n x) := by
  simp only [truthTableMatrix, reindex_apply, submatrix_apply, zeroSumMatrix_apply, map_sum,
    ← bitEquiv_symm_apply, RingEquiv.apply_symm_apply, truthTable_symm_apply]
  exact sum_congr (by ext; simp) fun _ _ => rfl

/-- The entries cost `4 · 2 ^ n + 1` gates each. -/
private theorem synthesis_entryBits_truthTableMatrix (n a : ℕ) :
    Synthesis interpretation (inputs (2 ^ n)) (entryBits (truthTableMatrix n a))
      (n.choose a * n.choose a * (4 * 2 ^ n + 1)) := by
  set e := subsetEquiv n a
  let S : Fin (n.choose a) × Fin (n.choose a) → Finset (BitString n) := fun p =>
    univ.filter fun x => ∀ k ∈ (e.symm p.1).1 ∪ (e.symm p.2).1, x k = false
  have h := Synthesis.family (I := interpretation) (s := inputs (2 ^ n))
    (fun p (T : BitString (2 ^ n)) => ∑ x ∈ S p, T (BitString.equivFin n x))
    (fun _ => 4 * 2 ^ n + 1) fun p => by
      refine (Synthesis.sum (S p) (fun x (T : BitString (2 ^ n)) => T (BitString.equivFin n x))
        (fun _ => 0) fun x _ =>
          Synthesis.of_mem (s := inputs (2 ^ n)) ⟨BitString.equivFin n x, rfl⟩).mono
        Set.Subset.rfl Set.Subset.rfl ?_
      have hS : (S p).card ≤ 2 ^ n := (card_filter_le _ _).trans (by simp [BitString])
      simp only [zero_add, sum_const, smul_eq_mul]
      omega
  refine h.mono Set.Subset.rfl ?_ (by simp [mul_comm])
  intro f hf
  obtain ⟨i, j, rfl⟩ := mem_entryBits.mp hf
  exact ⟨(i, j), funext fun T => (bitEquiv_truthTableMatrix n a T i j).symm⟩

/-! ### Constructivity -/

/-- **The rank test from truth tables**: De Morgan circuits with `173 · 8 ^ n` gates decide the rank
test at any level from the truth table, of length `2 ^ n`. Only the number of gates is bounded;
depth is not certified. -/
theorem synthesis_truthTableTest_rankTest (n a : ℕ) :
    Synthesis interpretation (inputs (2 ^ n)) {truthTableTest (rankTest n a)} (173 * 8 ^ n) := by
  set N := n.choose a
  have h := synthesis_le_rank_of_synthesis (truthTableMatrix n a)
    (synthesis_entryBits_truthTableMatrix n a) (t := (N + 1) / 2) (by omega)
  refine (Synthesis.congr_iff h fun T => ?_).mono Set.Subset.rfl Set.Subset.rfl ?_
  · rw [truthTableTest_eq_true_iff, mem_rankTest, decide_eq_true_iff, rank_truthTableMatrix]
    omega
  · have hN : N ≤ 2 ^ n := Nat.choose_le_two_pow n a
    have hM : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h8 : 8 ^ n = 2 ^ n * 2 ^ n * 2 ^ n := by
      rw [← mul_pow, ← mul_pow]
      norm_num
    rw [h8]
    calc N * N * (4 * 2 ^ n + 1) + 14 * (N + 1) * (N + 1) * (N + N + 1)
        ≤ 2 ^ n * 2 ^ n * (4 * 2 ^ n + 1) +
            14 * (2 ^ n + 2 ^ n) * (2 ^ n + 2 ^ n) * (2 ^ n + 2 ^ n + 2 ^ n) := by
          gcongr
      _ ≤ 173 * (2 ^ n * 2 ^ n * 2 ^ n) := by
          have hsq : 2 ^ n * 2 ^ n ≤ 2 ^ n * 2 ^ n * 2 ^ n := Nat.le_mul_of_pos_right _ hM
          nlinarith

/-- The circuit complexity of the rank test from truth tables is at most `173 · 8 ^ n`. -/
theorem complexity_truthTableTest_rankTest_le (n a : ℕ) :
    complexity interpretation (single (truthTableTest (rankTest n a))) ≤ 173 * 8 ^ n :=
  (synthesis_truthTableTest_rankTest n a).complexity_le

/-- The **rank property** along a level function `a`: on `n` inputs, the rank test at level
`a n`. -/
def rankProperty (a : ℕ → ℕ) : ∀ n, Set (BooleanFunction n) := fun n => rankTest n (a n)

/-- On `n` inputs, the rank property is the rank test at level `a n`. -/
@[simp] theorem rankProperty_apply (a : ℕ → ℕ) (n : ℕ) : rankProperty a n = rankTest n (a n) :=
  (rfl)

/-- **Constructivity**: along any level function, the truth tables of the rank property form a
language in `P/poly`, decided with at most `173 N ^ 3` gates at length `N = 2 ^ n`. -/
theorem truthTableLanguage_rankProperty_mem_PPoly (a : ℕ → ℕ) :
    truthTableLanguage (rankProperty a) ∈ PPoly :=
  truthTableLanguage_mem_PPoly_of_synthesis _ (cost := fun N => 173 * N ^ 3)
    ((PolynomiallyBounded.const 173).mul (PolynomiallyBounded.id.pow 3)) fun n =>
      (synthesis_truthTableTest_rankTest n (a n)).mono Set.Subset.rfl Set.Subset.rfl
        (le_of_eq (by rw [← pow_mul, mul_comm n 3, pow_mul]; norm_num))

/-- **Largeness**: along any level function, at least half of the Boolean functions on `n` inputs
have the rank property, so it is large with `c = 1`. -/
theorem isLarge_rankProperty (a : ℕ → ℕ) : IsLarge (rankProperty a) := by
  refine ⟨1, (eventually_ge_atTop 1).mono fun n hn => ?_⟩
  have h2 : 2 ≤ 2 ^ (1 * n) := by
    rw [one_mul]
    exact Nat.le_self_pow (by omega) 2
  exact (two_pow_two_pow_le_two_mul_ncard_rankTest n (a n)).trans (Nat.mul_le_mul_right _ h2)

/-- **The rank property is `P/poly`-natural** along any level function: it is large, and its truth
tables are decided by polynomial-size circuits. Along the middle level it is also useful against
`AC⁰[2]`
(`Cslib.Circuits.Boolean.Razborov.isNatural_PPoly_and_isUseful_AC0Mod_two_rankProperty`). -/
theorem isNatural_PPoly_rankProperty (a : ℕ → ℕ) : IsNatural PPoly (rankProperty a) :=
  ⟨rankProperty a, fun _ => le_rfl, isLarge_rankProperty a,
    truthTableLanguage_rankProperty_mem_PPoly a⟩

end Cslib.Circuits.Boolean.Razborov
