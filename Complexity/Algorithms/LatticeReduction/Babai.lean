/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.LatticeReduction.LLL
public import Complexity.Algorithms.LatticeReduction.NearestPlane

/-!
# Babai's nearest-plane algorithm

Babai's nearest-plane algorithm ([Babai1986]; [Regev2004], Lecture 3, §1) on the rows of an
integer matrix `B : Vector (Vector ℤ m) n` and an integer target `t ∈ ℤᵐ`, with exact rational
Gram–Schmidt vectors `b*ⱼ`. Starting from `r = t`, for `j = n - 1, …, 0` it rounds the
Gram–Schmidt coordinate `cⱼ = ⌊⟨r, b*ⱼ⟩ / ⟨b*ⱼ, b*ⱼ⟩⌉` and sets `r ← r - cⱼ bⱼ`; the output is
`t - r` (`Cslib.Algorithms.LatticeReduction.nearestPlane`). It is a lattice point, and every
Gram–Schmidt coordinate of `t - (t - r) = r` lies in `[-1/2, 1/2]`
(`Cslib.Algorithms.LatticeReduction.isNearestPlane_nearestPlane`).

`Cslib.Algorithms.LatticeReduction.babai` runs `nearestPlane` on the output of the LLL algorithm
`Cslib.Algorithms.LatticeReduction.lll`. For linearly independent rows, the output `y` satisfies
`|y - t|² ≤ 2ⁿ |v - t|²` for every lattice vector `v`
(`Cslib.Algorithms.LatticeReduction.babai_dotProduct_le`): it solves the closest vector problem
within a factor `2^{n/2}`, [Regev2004], Lecture 3, Lemma 6.

The target is an integer vector, as in [Regev2004]; the abstract bound
`Cslib.Algorithms.LatticeReduction.IsNearestPlane.norm_sq_le` holds for arbitrary real targets.

## Main definitions

* `Cslib.Algorithms.LatticeReduction.nearestPlane`: the nearest-plane loop.
* `Cslib.Algorithms.LatticeReduction.babai`: LLL reduction followed by the nearest-plane loop.

## Main results

* `Cslib.Algorithms.LatticeReduction.isNearestPlane_nearestPlane`: the output of the loop
  satisfies the nearest-plane condition.
* `Cslib.Algorithms.LatticeReduction.babai_mem_span`: the output of `babai` is a lattice vector.
* `Cslib.Algorithms.LatticeReduction.babai_dotProduct_le`: the approximation factor `2^{n/2}`.

The running time is not formalized: the loop costs `O(n m)` rational operations after the
Gram–Schmidt computation, but there is no cost model here, and the running time of `lll` is itself
not yet bounded.

## References

* [L. Babai, *On Lovász' lattice reduction and the nearest lattice point problem*][Babai1986]
* [O. Regev, *Lattices in Computer Science*, lecture notes][Regev2004]
-/

public section

namespace Cslib.Algorithms.LatticeReduction

open InnerProductSpace

variable {m n : ℕ}

/-- The residual of the nearest-plane loop after the rounds `j = k - 1, …, 0`: for each `j`,
round `cⱼ = ⌊⟨r, b*ⱼ⟩ / ⟨b*ⱼ, b*ⱼ⟩⌉` with the Gram–Schmidt rows `G` and set `r ← r - cⱼ bⱼ`. -/
def nearestPlaneAux (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n) :
    ℕ → Vector ℤ m → Vector ℤ m
  | 0, r => r
  | k + 1, r =>
    if h : k < n then
      let c : ℤ := round (projCoeff (fun l : Fin m => G[k][l]) (fun l : Fin m => (r[l] : ℚ)))
      nearestPlaneAux G B k (Vector.ofFn fun l => r[l] - c * B[k][l])
    else nearestPlaneAux G B k r

/-- Babai's nearest-plane algorithm ([Babai1986]; [Regev2004], Lecture 3, §1) on the rows of
`B` and the target `t`, without the preliminary basis reduction. -/
def nearestPlane (B : Vector (Vector ℤ m) n) (t : Vector ℤ m) : Vector ℤ m :=
  let r := nearestPlaneAux (gramSchmidtRows B) B n t
  Vector.ofFn fun l => t[l] - r[l]

/-- Babai's algorithm: LLL reduction ([LenstraLenstraLovasz1982]) followed by the nearest-plane
loop. -/
def babai (B : Vector (Vector ℤ m) n) (t : Vector ℤ m) : Vector ℤ m :=
  nearestPlane (lll B) t

/-- The loop invariant: `r - nearestPlaneAux G B k r = ∑ⱼ eⱼ bⱼ` with `eⱼ = 0` for `j ≥ k`, and
the Gram–Schmidt coordinates of the output at `j < k` lie in `[-1/2, 1/2]`. -/
theorem nearestPlaneAux_spec {G : Vector (Vector ℚ m) n} {B : Vector (Vector ℤ m) n}
    (hG : IsGramSchmidtRows G B) :
    ∀ (k : ℕ) (r : Vector ℤ m), k ≤ n → ∃ e : Fin n → ℤ, (∀ i : Fin n, k ≤ (i : ℕ) → e i = 0) ∧
      r.get - (nearestPlaneAux G B k r).get = ∑ i, e i • rows B i ∧
      ∀ j : Fin n, (j : ℕ) < k →
        |inner ℝ (gramSchmidt ℝ (realRows B) j) (intToEuclidean (nearestPlaneAux G B k r).get)| ≤
          ‖gramSchmidt ℝ (realRows B) j‖ ^ 2 / 2 := by
  intro k
  induction k with
  | zero =>
    intro r _
    refine ⟨0, fun _ _ => rfl, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    simp [nearestPlaneAux]
  | succ k ih =>
    intro r hk
    have hkn : k < n := hk
    set kk : Fin n := ⟨k, hkn⟩ with hkk
    set c : ℤ := round (projCoeff (fun l : Fin m => G[k][l]) (fun l : Fin m => (r[l] : ℚ)))
      with hc
    set r1 : Vector ℤ m := Vector.ofFn fun l => r[l] - c * B[k][l] with hr1
    have hstep : nearestPlaneAux G B (k + 1) r = nearestPlaneAux G B k r1 := by
      simp only [nearestPlaneAux, hkn, dite_true]
      rfl
    rw [hstep]
    obtain ⟨e, he, hsum, hbound⟩ := ih r1 hkn.le
    have hr1' : r.get - r1.get = c • rows B kk := by
      funext l
      change r[(l : ℕ)] - r1[(l : ℕ)] = c * rows B kk l
      simp [hr1, rows_apply, hkk]
    refine ⟨Function.update e kk c, ?_, ?_, ?_⟩
    · intro i hi
      rw [Function.update_of_ne (fun h => by rw [h] at hi; simp [hkk] at hi)]
      exact he i (by omega)
    · have : r.get - (nearestPlaneAux G B k r1).get =
          (r.get - r1.get) + (r1.get - (nearestPlaneAux G B k r1).get) := by abel
      rw [this, hsum, hr1']
      have hupd : Function.update e kk c = e + Pi.single kk (c - e kk) := by
        funext i
        by_cases h : i = kk
        · subst h; simp
        · simp [h]
      rw [hupd]
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [he kk le_rfl, sub_zero, add_comm]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hbound j hj
      obtain rfl : j = kk := Fin.ext hj
      set g := gramSchmidt ℝ (realRows B) kk with hg
      set out := nearestPlaneAux G B k r1 with hout
      -- `⟪b*ₖ, out⟫ = ⟪b*ₖ, r₁⟫`, since `r₁ - out` only involves rows below `k`
      have hRout : intToEuclidean out.get =
          intToEuclidean r1.get - ∑ i, e i • realRows B i := by
        have h := congrArg intToEuclidean hsum
        rw [map_sub, map_sum] at h
        simp only [map_zsmul, ← realRows_eq_intToEuclidean] at h
        rw [← h]
        abel
      have hRr1 : intToEuclidean r1.get = intToEuclidean r.get - c • realRows B kk := by
        have h := congrArg intToEuclidean hr1'
        rw [map_sub, map_zsmul, ← realRows_eq_intToEuclidean] at h
        rw [← h]
        abel
      have hin1 : inner ℝ g (∑ i, e i • realRows B i) = 0 := by
        rw [hg, inner_gramSchmidt_sum_zsmul _ e fun i hi => he i (by
          have := Fin.lt_def.1 hi; simp [hkk] at this; omega), he kk (by simp [hkk]),
          Int.cast_zero, zero_mul]
      have hin2 : inner ℝ g (c • realRows B kk) = c * ‖g‖ ^ 2 := by
        rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hg, inner_gramSchmidt_self_right]
        rfl
      rw [hRout, inner_sub_right, hin1, sub_zero, hRr1, inner_sub_right, hin2]
      -- the rounding step
      have hcast : ((projCoeff (fun l : Fin m => G[k][l]) (fun l : Fin m => (r[l] : ℚ)) : ℚ) : ℝ) =
          inner ℝ g (intToEuclidean r.get) / ‖g‖ ^ 2 := by
        rw [cast_projCoeff]
        have hGk : ratToEuclidean (fun l : Fin m => G[k][l]) = g := hG.ratToEuclidean_eq kk
        rw [hGk, intToEuclidean_eq_ratToEuclidean]
        rfl
      have hround : (c : ℝ) = round (inner ℝ g (intToEuclidean r.get) / ‖g‖ ^ 2) := by
        rw [hc, ← hcast, Rat.round_cast]
      rcases eq_or_ne g 0 with h0 | h0
      · simp [h0]
      have hN : 0 < ‖g‖ ^ 2 := by positivity
      have hr := abs_sub_round (inner ℝ g (intToEuclidean r.get) / ‖g‖ ^ 2)
      rw [← hround] at hr
      have heq : inner ℝ g (intToEuclidean r.get) - c * ‖g‖ ^ 2 =
          (inner ℝ g (intToEuclidean r.get) / ‖g‖ ^ 2 - c) * ‖g‖ ^ 2 := by
        field_simp
      rw [heq, abs_mul, abs_of_pos hN]
      nlinarith

/-- The output of the nearest-plane loop: `t - nearestPlane B t` is the residual of the loop, so
`nearestPlane B t = ∑ⱼ eⱼ bⱼ` for some integers `eⱼ`, and every Gram–Schmidt coordinate of
`t - nearestPlane B t` lies in `[-1/2, 1/2]`. -/
theorem nearestPlane_spec (B : Vector (Vector ℤ m) n) (t : Vector ℤ m) :
    ∃ e : Fin n → ℤ, (nearestPlane B t).get = ∑ i, e i • rows B i ∧
      ∀ j : Fin n, |inner ℝ (gramSchmidt ℝ (realRows B) j)
        (intToEuclidean (t.get - (nearestPlane B t).get))| ≤
          ‖gramSchmidt ℝ (realRows B) j‖ ^ 2 / 2 := by
  obtain ⟨e, -, hsum, hbound⟩ :=
    nearestPlaneAux_spec (isGramSchmidtRows_gramSchmidtRows B) n t le_rfl
  have hout : (nearestPlane B t).get = t.get - (nearestPlaneAux (gramSchmidtRows B) B n t).get := by
    funext l
    change (nearestPlane B t)[(l : ℕ)] = _
    simp only [nearestPlane, Vector.getElem_ofFn]
    rfl
  refine ⟨e, by rw [hout, hsum], fun j => ?_⟩
  rw [hout, sub_sub_cancel]
  exact hbound j j.isLt

theorem mem_span_realRows_of_eq_sum {B : Vector (Vector ℤ m) n} {v : Fin m → ℤ} {e : Fin n → ℤ}
    (h : v = ∑ i, e i • rows B i) :
    intToEuclidean v ∈ Submodule.span ℤ (Set.range (realRows B)) := by
  rw [span_realRows]
  refine Submodule.mem_map_of_mem ?_
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The nearest-plane loop satisfies the nearest-plane condition for the rows of `B`, with the
target and output embedded in `ℝᵐ`. -/
theorem isNearestPlane_nearestPlane (B : Vector (Vector ℤ m) n) (t : Vector ℤ m) :
    IsNearestPlane (realRows B) (intToEuclidean t.get) (intToEuclidean (nearestPlane B t).get) := by
  obtain ⟨e, he, hbound⟩ := nearestPlane_spec B t
  refine ⟨mem_span_realRows_of_eq_sum he, fun j => ?_⟩
  rw [← map_sub]
  exact hbound j

/-- The output of `babai` lies in the lattice spanned by the rows of `B`. -/
theorem babai_mem_span (B : Vector (Vector ℤ m) n) (t : Vector ℤ m) :
    (babai B t).get ∈ Submodule.span ℤ (Set.range (rows B)) := by
  obtain ⟨e, he, -⟩ := nearestPlane_spec (lll B) t
  rw [babai, he, ← span_lll B]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Babai's algorithm solves the closest vector problem within a factor `2^{n/2}`
([Regev2004], Lecture 3, Lemma 6): for linearly independent integer rows `b₀, …, bₙ₋₁` and an
integer target `t`, the output `y` satisfies `|y - t|² ≤ 2ⁿ |v - t|²` for every vector `v` of the
lattice spanned by the rows. -/
theorem babai_dotProduct_le (B : Vector (Vector ℤ m) n) (hB : LinearIndependent ℝ (realRows B))
    (t : Vector ℤ m) {v : Fin m → ℤ} (hv : v ∈ Submodule.span ℤ (Set.range (rows B))) :
    dotProduct ((babai B t).get - t.get) ((babai B t).get - t.get) ≤
      2 ^ n * dotProduct (v - t.get) (v - t.get) := by
  obtain ⟨hred, -⟩ := isReduced_lll B hB
  have hnp := isNearestPlane_nearestPlane (lll B) t
  have hmem : intToEuclidean v ∈ Submodule.span ℤ (Set.range (realRows (lll B))) := by
    rw [span_realRows, span_lll]
    exact Submodule.mem_map_of_mem hv
  have h := hnp.norm_sq_le_two_pow_mul hred hmem
  rw [norm_sub_rev, ← map_sub, norm_sq_intToEuclidean, norm_sub_rev, ← map_sub,
    norm_sq_intToEuclidean] at h
  rw [babai]
  exact_mod_cast h

end Cslib.Algorithms.LatticeReduction
