/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Algebraic.Boolean
import Complexity.Foundations.BooleanAnalysis.AffineDegree
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# A degree lower bound for subset sum

The **subset-sum polynomial** `m - ∑ᵢ cᵢ xᵢ` (`Cslib.Logic.PL.Algebraic.subsetSumPoly`) over a field
`F`, with the Boolean axioms, asks for a subset of the coefficients `cᵢ` summing to `m`.
Theorem 5.1 of Impagliazzo, Pudlák and Sgall [ImpagliazzoPudlakSgall1999] states that for nonzero
real `c₁, …, cₙ` and arbitrary real `m`, this polynomial has no polynomial calculus refutation of
degree `⌈n/2⌉`. Here this is `Cslib.Logic.PL.PC.not_refutableInDegree_subsetSumPoly`, for the
polynomial calculus proofs `Cslib.Logic.PL.PC.IsProof` with the Boolean axioms as inputs. Since
the Nullstellensatz proofs `Cslib.Logic.PL.NS.IsProof` are simulated in the same degree
(`Cslib.Logic.PL.PC.RefutableInDegree.of_ns`), the bound also holds for Nullstellensatz
(`Cslib.Logic.PL.NS.not_refutableInDegree_subsetSumPoly`). When `m` is not a subset sum of the
`cᵢ`, the system is refutable in degree `n + 1` by completeness
(`Cslib.Logic.PL.PC.refutableInDegree_subsetSumPoly_iff`), so this is a genuine degree lower bound.
For `c = 1` and `m > n`, Theorem 4.2 of the same paper gives a refutation of degree `⌈n/2⌉ + 1`,
under a condition on the characteristic. The source notes that this matches the lower bound over
`ℝ`. That upper bound is not formalized here.

The statement here holds over every field in which `⌈n/2⌉!` is nonzero, so in characteristic zero
and in every characteristic larger than `⌈n/2⌉`; the source states it over `ℝ`. This is a mild
generalization of the source statement, with the same proof: Lemma 5.2 is applied only to
functions of degree below `⌈n/2⌉`, and needs `1, …, deg r + 1` to be nonzero.

The proof follows the source, through the invariant method
(`Cslib.Logic.PL.PC.IsProof.mem_of_degree_le`). Let `L x = m - ∑ᵢ cᵢ xᵢ`, and let `M` be the
polynomials that agree on the cube with `L * r` for a function `r` of degree at most `d - 1`.

* `M` is a submodule containing the subset-sum polynomial (`r = 1`) and the Boolean axioms
  (`r = 0`).
* If `p ∈ M` and `X i * p` has degree at most `d`, then `p` has degree at most `d - 1`, and so
  has `L * r`. Lemma 5.2 of the source (`Cslib.BitString.totalDegree_affine_mul`) bounds the
  degree of `r` by `d - 2`, which leaves room for the factor `xᵢ`.
* A refutation would put `1` in `M`, so `1 = L * r` on the cube with `r ≠ 0`. Lemma 5.2 would
  then give the constant `1` degree at least one.

## Main definitions

* `Cslib.Logic.PL.Algebraic.subsetSumPoly`: the polynomial `m - ∑ᵢ cᵢ xᵢ`.

## Main results

* `Cslib.Logic.PL.Algebraic.isBoolSolution_subsetSumPoly_iff`: the `0/1` solutions are the subsets
  summing to `m`.
* `Cslib.Logic.PL.PC.not_refutableInDegree_subsetSumPoly`: Theorem 5.1 of
  [ImpagliazzoPudlakSgall1999], over fields with `⌈n/2⌉! ≠ 0`.
* `Cslib.Logic.PL.NS.not_refutableInDegree_subsetSumPoly`: the same bound for Nullstellensatz.
* `Cslib.Logic.PL.PC.refutableInDegree_subsetSumPoly_iff`: refutability in degree `n + 1`
  exactly when no subset sums to `m`.

## References

* [R. Impagliazzo, P. Pudlák, J. Sgall, *Lower bounds for the polynomial calculus and the Gröbner
  basis algorithm*][ImpagliazzoPudlakSgall1999]
-/

open MvPolynomial Cslib.BitString

namespace Cslib.Logic.PL

namespace Algebraic

variable {ι F : Type*} [Field F] [Fintype ι]

/-- The **subset-sum polynomial** `m - ∑ᵢ cᵢ xᵢ`, whose `0/1` zeros are the subsets of the
coefficients `cᵢ` summing to `m`. -/
@[expose] public noncomputable def subsetSumPoly (c : ι → F) (m : F) : MvPolynomial ι F :=
  C m - ∑ i, C (c i) * X i

/-- The subset-sum polynomial has degree at most one. -/
public theorem totalDegree_subsetSumPoly_le (c : ι → F) (m : F) :
    (subsetSumPoly c m).totalDegree ≤ 1 := by
  refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega)
    ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)))
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]; exact (totalDegree_monomial_le _ _).trans (by simp))

/-- The `0/1` solutions of the subset-sum polynomial are the subsets of the coefficients summing
to `m`. -/
public theorem isBoolSolution_subsetSumPoly_iff (c : ι → F) (m : F) (x : ι → Bool) :
    IsBoolSolution [subsetSumPoly c m] x ↔ ∑ i, c i * bitVal F (x i) = m := by
  simp only [IsBoolSolution, List.mem_singleton, forall_eq, subsetSumPoly, map_sub, eval_C,
    map_sum, map_mul, eval_X]
  rw [sub_eq_zero, eq_comm]

/-- Evaluation on the cube, as an algebra map into functions on the cube. -/
private noncomputable abbrev cube : MvPolynomial ι F →ₐ[F] ((ι → Bool) → F) :=
  aeval fun i (x : ι → Bool) => bitVal F (x i)

omit [Fintype ι] in
private theorem cube_mem_lowDegree (p : MvPolynomial ι F) :
    cube p ∈ lowDegree F ι p.totalDegree := by
  rw [lowDegree_eq_map_restrictTotalDegree]
  exact ⟨p, (mem_restrictTotalDegree _ _ _).2 le_rfl, rfl⟩

private theorem cube_subsetSumPoly (c : ι → F) (m : F) :
    cube (subsetSumPoly c m) = fun x => m - ∑ i, c i * bitVal F (x i) := by
  funext x
  simp [subsetSumPoly, Finset.sum_apply]

omit [Fintype ι] in
private theorem cube_boolAxiom (i : ι) : cube (boolAxiom i : MvPolynomial ι F) = 0 := by
  funext x
  simp [boolAxiom, bitVal_pow _ two_ne_zero]

/-- The invariant of the proof of Theorem 5.1: the polynomials that agree on the cube with
`L * r` for some `r` of degree at most `k`, where `L x = m - ∑ᵢ cᵢ xᵢ`. -/
private noncomputable def invariant (c : ι → F) (m : F) (k : ℕ) :
    Submodule F (MvPolynomial ι F) :=
  (Submodule.map (LinearMap.mulLeft F (fun x : ι → Bool => m - ∑ i, c i * bitVal F (x i)))
    (lowDegree F ι k)).comap cube.toLinearMap

private theorem mem_invariant {c : ι → F} {m : F} {k : ℕ} {p : MvPolynomial ι F} :
    p ∈ invariant c m k ↔
      ∃ r ∈ lowDegree F ι k, (fun x => m - ∑ i, c i * bitVal F (x i)) * r = cube p := by
  simp [invariant]

/-- Multiplying by a variable stays in the invariant within degree `d`, when `2 (d - 1) < n`. -/
private theorem mulVar_mem_invariant {c : ι → F} (hc : ∀ i, c i ≠ 0) (m : F) {d : ℕ}
    (hd : 2 * (d - 1) < Fintype.card ι)
    (hF : ∀ j : ℕ, 0 < j → j ≤ (Fintype.card ι + 1) / 2 → (j : F) ≠ 0) (i : ι)
    (p : MvPolynomial ι F)
    (hp : p ∈ invariant c m (d - 1)) (hXp : (X i * p).totalDegree ≤ d) :
    X i * p ∈ invariant c m (d - 1) := by
  obtain ⟨r, hr, hp⟩ := mem_invariant.1 hp
  rw [mem_invariant]
  by_cases hp0 : p = 0
  · exact ⟨0, Submodule.zero_mem _, by rw [mul_zero, hp0, mul_zero, map_zero]⟩
  by_cases hr0 : r = 0
  · exact ⟨0, Submodule.zero_mem _, by rw [map_mul, ← hp, hr0, mul_zero, mul_zero]⟩
  -- `p` has degree at most `d - 1`, hence so has `L * r`, and `r` has degree at most `d - 2`
  have hdeg : p.totalDegree ≤ d - 1 := by
    rw [totalDegree_mul_of_isDomain (X_ne_zero i) hp0, totalDegree_X] at hXp
    omega
  have hrk : BitString.totalDegree r ≤ d - 1 := totalDegree_le_of_mem_lowDegree hr
  have h52 := totalDegree_affine_mul hc m (fun j hj hjr => hF j hj (by omega)) hr0 (by omega)
  have hLr : BitString.totalDegree ((fun x => m - ∑ i, c i * bitVal F (x i)) * r) ≤ d - 1 := by
    rw [hp]
    exact totalDegree_le_of_mem_lowDegree (lowDegree_mono hdeg (cube_mem_lowDegree p))
  refine ⟨(fun x => bitVal F (x i)) * r, ?_, ?_⟩
  · exact lowDegree_mono (by omega)
      (mul_mem_lowDegree (bitVal_mem_lowDegree i) (mem_lowDegree_totalDegree r))
  · rw [map_mul, ← hp, aeval_X]
    ring

end Algebraic

open Algebraic

variable {ι F : Type*} [Field F] [Fintype ι]

/-- **Theorem 5.1 of [ImpagliazzoPudlakSgall1999].** Let `c₁, …, cₙ` be nonzero, `n ≥ 1`, and `m`
arbitrary, over a field in which `⌈n/2⌉!` is nonzero. Then the subset-sum polynomial `m - ∑ᵢ cᵢ xᵢ`,
with the Boolean axioms, has no polynomial calculus refutation of degree `⌈n/2⌉ = (n + 1) / 2`.
The source states the theorem over `ℝ`. For `n = 0` and `m ≠ 0` the constant `m` refutes itself
in degree `0`. -/
public theorem PC.not_refutableInDegree_subsetSumPoly [Nonempty ι] {c : ι → F}
    (hc : ∀ i, c i ≠ 0) (m : F) (hF : (((Fintype.card ι + 1) / 2).factorial : F) ≠ 0) {d : ℕ}
    (hd : d ≤ (Fintype.card ι + 1) / 2) :
    ¬ PC.RefutableInDegree ([subsetSumPoly c m] ++ boolAxioms ι F) d := by
  classical
  rintro ⟨ls, hls, h1, hdeg⟩
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hF' : ∀ j : ℕ, 0 < j → j ≤ (Fintype.card ι + 1) / 2 → (j : F) ≠ 0 := by
    intro j hj hjn hj0
    apply hF
    obtain ⟨q, hq⟩ := Nat.dvd_factorial hj hjn
    rw [hq, Nat.cast_mul, hj0, zero_mul]
  have hmem := hls.mem_of_degree_le hdeg (invariant c m (d - 1)) ?_
    (fun i p hp hXp => mulVar_mem_invariant hc m (by omega) hF' i p hp hXp) 1 h1
  · obtain ⟨r, hr, h1⟩ := mem_invariant.1 hmem
    rw [map_one] at h1
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at h1
      exact zero_ne_one h1
    have hrd := totalDegree_le_of_mem_lowDegree hr
    have h52 := totalDegree_affine_mul hc m (fun j hj hjr => hF' j hj (by omega)) hr0 (by omega)
    rw [h1] at h52
    have h0 : BitString.totalDegree (1 : (ι → Bool) → F) = 0 :=
      Nat.le_zero.1 (totalDegree_le_of_mem_lowDegree (one_mem_lowDegree 0))
    omega
  · intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · rw [List.mem_singleton] at hf
      subst hf
      exact mem_invariant.2 ⟨1, one_mem_lowDegree _, by rw [mul_one, cube_subsetSumPoly]⟩
    · obtain ⟨i, rfl⟩ := mem_boolAxioms.1 hf
      exact mem_invariant.2 ⟨0, Submodule.zero_mem _, by rw [cube_boolAxiom, mul_zero]⟩

/-- **Theorem 5.1 of [ImpagliazzoPudlakSgall1999] for Nullstellensatz.** Under the hypotheses of
`Cslib.Logic.PL.PC.not_refutableInDegree_subsetSumPoly`, the subset-sum polynomial, with the
Boolean axioms, has no Nullstellensatz refutation of degree `⌈n/2⌉`. -/
public theorem NS.not_refutableInDegree_subsetSumPoly [Nonempty ι] {c : ι → F}
    (hc : ∀ i, c i ≠ 0) (m : F) (hF : (((Fintype.card ι + 1) / 2).factorial : F) ≠ 0) {d : ℕ}
    (hd : d ≤ (Fintype.card ι + 1) / 2) :
    ¬ NS.RefutableInDegree ([subsetSumPoly c m] ++ boolAxioms ι F) d := fun h =>
  PC.not_refutableInDegree_subsetSumPoly hc m hF hd (.of_ns h)

/-- The subset-sum polynomial, with the Boolean axioms, has a polynomial calculus refutation of
degree `n + 1` exactly when no subset of the coefficients sums to `m`. -/
public theorem PC.refutableInDegree_subsetSumPoly_iff (c : ι → F) (m : F) :
    PC.RefutableInDegree ([subsetSumPoly c m] ++ boolAxioms ι F) (Fintype.card ι + 1) ↔
      ∀ x : ι → Bool, ∑ i, c i * bitVal F (x i) ≠ m := by
  rw [PC.refutableInDegree_iff (by simpa using totalDegree_subsetSumPoly_le c m)]
  simp only [isBoolSolution_subsetSumPoly_iff]

end Cslib.Logic.PL
