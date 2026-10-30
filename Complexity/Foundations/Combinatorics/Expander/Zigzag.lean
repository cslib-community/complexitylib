/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Loops
public import Complexity.Foundations.Combinatorics.Expander.Tensor
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt

/-!
# The zig-zag product of rotation maps

The **zig-zag product** `G.zigzag H` of a `D`-regular graph `G` with a graph `H` on the labels `D`
of `G` is a graph on `V × D` with the square of the degree of `H`
[Reingold, Vadhan and Wigderson, Section 3][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]
[Hoory, Linial and Wigderson, Section 9.3][HooryLinialWigderson2006]:
`λ(G ⓩ H) ≤ λ(G) + λ(H) + λ(H) ^ 2` and `λ(G ⓩ H) ≤ 1 - (1 - λ(G)) (1 - λ(H)) ^ 2`.

The zig-zag theorem is proved as in
[Reingold, Vadhan and Wigderson, Section 4.1][ReingoldVadhanWigderson2002]. The walk operator of
`G ⓩ H` is `B̃ Ã B̃`, where `B̃ = I ⊗ W_H` is the walk on the copies `{v} × D` of `H`, the walk
operator of `(loops V Unit).tensor H`, and `Ã` permutes the vertices by the rotation map of `G`. A
function on `V × D` splits into its averages over the copies of `H` and a part of average zero on
every copy; `B̃` fixes the first and shrinks the second by `λ(H)`, while on the first `Ã` acts as
the walk on `G`. This bounds `𝔼 h · W f` for every `h` and every `f` of expectation zero, and with
`h = W f` it bounds `W f`: as `λ` is an operator norm, no eigenvectors are needed.

## Main definitions

* `Cslib.RotationMap.zigzagRot`: the underlying functional rotation program, shared with its
  efficiency certificate.
* `Cslib.RotationMap.zigzag`: the zig-zag product `G ⓩ H`.

## Main results

* `Cslib.RotationMap.walk_zigzag`: the walk operator of `G ⓩ H` is `B̃ Ã B̃`.
* `Cslib.RotationMap.spectralExpansion_zigzag_le`: **the zig-zag theorem**,
  `λ(G ⓩ H) ≤ λ(G) + λ(H) + λ(H) ^ 2`.
* `Cslib.RotationMap.spectralExpansion_zigzag_le_one_sub`,
  `Cslib.RotationMap.spectralExpansion_zigzag_lt_one`: the zig-zag product of two expanders is an
  expander.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open Fintype (expect_comp_fst
  expect_add_sq_of_expect_fiber_eq_zero exists_eq_add_expect_fiber_eq_zero
  expect_sq_le_of_expect_mul_le)
open Real (expect_mul_le_sqrt_mul_sqrt)
open scoped BigOperators

/-- A bound on a square root from a bound on its argument. -/
private theorem sqrt_le_mul_sqrt {x y c : ℝ} (hc : 0 ≤ c) (h : x ≤ c ^ 2 * y) :
    √x ≤ c * √y := by
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
  exact Real.sqrt_le_sqrt h

/-- For `g` of average zero over every copy of `H`, `λ(H) φ + (I ⊗ W_H) g` has norm at most `λ(H)`
times that of `φ + g`, where `φ` is a function of the first coordinate. -/
private theorem sqrt_expect_mul_add_walk_loops_tensor_sq_le {V V' D' : Type*}
    (H : RotationMap V' D') [Fintype V] [Fintype V'] [Fintype D'] [Nonempty V'] [Nonempty D']
    (φ : V → ℝ) {g : V × V' → ℝ} (hg : ∀ v, 𝔼 v', g (v, v') = 0) :
    √(𝔼 p, (H.spectralExpansion * φ p.1 + ((loops V Unit).tensor H).walk g p) ^ 2) ≤
      H.spectralExpansion * √(𝔼 v, φ v ^ 2 + 𝔼 p, g p ^ 2) := by
  refine sqrt_le_mul_sqrt H.spectralExpansion_nonneg ?_
  rw [expect_add_sq_of_expect_fiber_eq_zero (fun v ↦ H.spectralExpansion * φ v)
      (H.expect_walk_loops_tensor_eq_zero hg),
    expect_comp_fst (fun v ↦ (H.spectralExpansion * φ v) ^ 2), mul_add]
  simp only [mul_pow, ← mul_expect]
  gcongr
  exact H.expect_walk_loops_tensor_sq_le hg

/-- The bilinear estimate behind the zig-zag theorem: for nonnegative `b₁, b₂`,
`μ a₁ b₁ + ν (a₁ b₂ + a₂ b₁) + ν² a₂ b₂ ≤ (μ + ν + ν²) √(a₁² + a₂²) √(b₁² + b₂²)`. -/
private theorem add_mul_le_mul_sqrt_mul_sqrt {μ ν a₁ a₂ b₁ b₂ : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    a₁ * (μ * b₁) + a₁ * (ν * b₂) + ν * a₂ * b₁ + ν * a₂ * (ν * b₂) ≤
      (μ + ν + ν ^ 2) * (√(a₁ ^ 2 + a₂ ^ 2) * √(b₁ ^ 2 + b₂ ^ 2)) := by
  have hA₁ : a₁ ≤ √(a₁ ^ 2 + a₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hA₂ : a₂ ≤ √(a₁ ^ 2 + a₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hB₁ : b₁ ≤ √(b₁ ^ 2 + b₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hB₂ : b₂ ≤ √(b₁ ^ 2 + b₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h₁₁ := mul_le_mul hA₁ hB₁ hb₁ (Real.sqrt_nonneg _)
  have h₂₂ := mul_le_mul hA₂ hB₂ hb₂ (Real.sqrt_nonneg _)
  have h₁₂ : a₁ * b₂ + a₂ * b₁ ≤ √(a₁ ^ 2 + a₂ ^ 2) * √(b₁ ^ 2 + b₂ ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (a₁ * b₁ - a₂ * b₂)])
  nlinarith [mul_le_mul_of_nonneg_left h₁₁ hμ, mul_le_mul_of_nonneg_left h₁₂ hν,
    mul_le_mul_of_nonneg_left h₂₂ (sq_nonneg ν)]

/-- The bilinear estimate behind the second zig-zag bound: for `0 ≤ a ≤ A` and `0 ≤ b ≤ B`,
`(1 - ν)² μ a b + (1 - ν) ν (a B + A b) + ν² A B ≤ (1 - (1 - μ) (1 - ν)²) A B`. -/
private theorem mul_add_le_one_sub_mul {μ ν a b A B : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hν₁ : ν ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haA : a ≤ A) (hbB : b ≤ B) :
    (1 - ν) ^ 2 * (a * (μ * b)) + (1 - ν) * (a * (ν * B)) + (1 - ν) * (ν * A * b) +
        ν * A * (ν * B) ≤ (1 - (1 - μ) * (1 - ν) ^ 2) * (A * B) := by
  have h₁ : a * b ≤ A * B := mul_le_mul haA hbB hb (ha.trans haA)
  have h₂ : a * B ≤ A * B := mul_le_mul_of_nonneg_right haA (hb.trans hbB)
  have h₃ : A * b ≤ A * B := mul_le_mul_of_nonneg_left hbB (ha.trans haA)
  have hν' : 0 ≤ 1 - ν := sub_nonneg.2 hν₁
  nlinarith [mul_le_mul_of_nonneg_left h₁ (mul_nonneg (sq_nonneg (1 - ν)) hμ),
    mul_le_mul_of_nonneg_left h₂ (mul_nonneg hν' hν),
    mul_le_mul_of_nonneg_left h₃ (mul_nonneg hν' hν)]

variable {V D E : Type*} (G : RotationMap V D) (H : RotationMap D E)

/-- Execute a zig-zag rotation, retaining the return labels of the zig and zag. -/
def zigzagRot (rotate : V × D → V × D) (cloud : D × E → D × E)
    (p : (V × D) × (E × E)) : (V × D) × (E × E) :=
  let a := cloud (p.1.2, p.2.1)
  let b := rotate (p.1.1, a.1)
  let c := cloud (b.2, p.2.2)
  ((b.1, c.1), (c.2, a.2))

/-- The **zig-zag product** `G ⓩ H`
[Reingold, Vadhan and Wigderson, Definition 3.1][ReingoldVadhanWigderson2002]
[Hoory, Linial and Wigderson, Section 9.3][HooryLinialWigderson2006] of a `D`-regular graph `G` on
`V` with a graph `H` on the labels `D` of `G`. Its vertices are the pairs `(v, k)`, the `k`-th edge
at `v`, grouped into the cloud `{v} × D` of `v`, and its labels are pairs of labels of `H`. The edge
`(i, j)` at `(v, k)` takes the edge `i` of `H` from `k` to `k'` inside the cloud ("zig"), crosses
the `k'`-th edge of `G` from `v` to `(w, ℓ')`, where it is the `ℓ'`-th edge at `w`, and takes the
edge `j` of `H` from `ℓ'` to `ℓ` inside the cloud of `w` ("zag"), ending at `(w, ℓ)`. -/
@[reducible]
def zigzag : RotationMap (V × D) (E × E) where
  rot := zigzagRot G.rot H.rot
  rot_involutive p := by simp [zigzagRot]

/-- The rotation map of `G ⓩ H`
[Reingold, Vadhan and Wigderson, Definition 3.1][ReingoldVadhanWigderson2002]: with
`(k', i') = H.rot (k, i)`, `(w, ℓ') = G.rot (v, k')` and `(ℓ, j') = H.rot (ℓ', j)`, the edge
`(i, j)` at `(v, k)` is the edge `(j', i')` at `(w, ℓ)`. -/
@[simp]
theorem rot_zigzag (v : V) (k : D) (i j : E) :
    (G.zigzag H).rot ((v, k), (i, j)) =
      (((G.rot (v, (H.rot (k, i)).1)).1, (H.rot ((G.rot (v, (H.rot (k, i)).1)).2, j)).1),
        ((H.rot ((G.rot (v, (H.rot (k, i)).1)).2, j)).2, (H.rot (k, i)).2)) :=
  rfl

/-- The neighbors in `G ⓩ H`: a step in `H`, a step in `G`, and a step in `H`. -/
theorem neighbor_zigzag (p : V × D) (i : E × E) :
    (G.zigzag H).neighbor p i =
      ((G.rot (p.1, H.neighbor p.2 i.1)).1, H.neighbor (G.rot (p.1, H.neighbor p.2 i.1)).2 i.2) :=
  rfl

variable [Fintype E]

/-- The walk operator of `G ⓩ H` is `B̃ Ã B̃`
[Reingold, Vadhan and Wigderson, Section 4.1][ReingoldVadhanWigderson2002], where `B̃ = I ⊗ W_H` is
the walk operator of `H` on every cloud and `Ã` is the permutation of the vertices `V × D` by the
rotation map of `G`. -/
theorem walk_zigzag :
    (G.zigzag H).walk =
      ((loops V Unit).tensor H).walk ∘ₗ LinearMap.funLeft ℝ ℝ G.rot ∘ₗ
        ((loops V Unit).tensor H).walk :=
  LinearMap.ext fun f ↦ funext fun p ↦ by
    rw [walk_apply (G.zigzag H), Fintype.expect_prod_type, LinearMap.comp_apply,
      LinearMap.comp_apply, walk_loops_tensor_apply, walk_apply H]
    simp only [LinearMap.funLeft_apply, walk_loops_tensor_apply]
    simp only [walk_apply]
    rfl

variable [Fintype V] [Fintype D]

/-- In the splitting of functions along the clouds, `⟨h, W f⟩ = ⟨B̃ h, Ã B̃ f⟩` where `B̃` fixes the
parts constant on the clouds. -/
private theorem expect_mul_walk_zigzag_eq [Nonempty E] (h₁ f₁ : V → ℝ) (h₂ f₂ : V × D → ℝ) :
    𝔼 p, (h₁ p.1 + h₂ p) * (G.zigzag H).walk (fun p ↦ f₁ p.1 + f₂ p) p =
      𝔼 p, (h₁ p.1 + ((loops V Unit).tensor H).walk h₂ p) *
        (f₁ (G.rot p).1 + ((loops V Unit).tensor H).walk f₂ (G.rot p)) := by
  rw [walk_zigzag, LinearMap.comp_apply, LinearMap.comp_apply,
    ((loops V Unit).tensor H).expect_mul_walk_comm, walk_loops_tensor_add, walk_loops_tensor_add]
  rfl

/-- On the functions constant on the clouds, `Ã` acts as the walk on `G`. -/
private theorem expect_mul_comp_rot_le (φ : V → ℝ) {ψ : V → ℝ} (hψ : 𝔼 v, ψ v = 0) :
    𝔼 p, φ p.1 * ψ (G.rot p).1 ≤ √(𝔼 v, φ v ^ 2) * (G.spectralExpansion * √(𝔼 v, ψ v ^ 2)) := by
  have : 𝔼 p, φ p.1 * ψ (G.rot p).1 = 𝔼 v, φ v * G.walk ψ v := by
    simp only [Fintype.expect_prod_type, walk_apply, mul_expect]
    rfl
  rw [this]
  refine (expect_mul_le_sqrt_mul_sqrt univ _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact sqrt_le_mul_sqrt G.spectralExpansion_nonneg (expect_walk_sq_le_spectralExpansion_sq_mul hψ)

/-- The zig-zag estimate in bilinear form: `𝔼 h · W f ≤ (λ(G) + λ(H) + λ(H)²) ‖h‖ ‖f‖` for `f` of
expectation zero. -/
private theorem expect_mul_walk_zigzag_le [Nonempty D] [Nonempty E] (h : V × D → ℝ)
    {f : V × D → ℝ} (hf : 𝔼 p, f p = 0) :
    𝔼 p, h p * (G.zigzag H).walk f p ≤
      (G.spectralExpansion + H.spectralExpansion + H.spectralExpansion ^ 2) *
        (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  obtain ⟨h₁, h₂, rfl, hh₂, -, hhh⟩ := exists_eq_add_expect_fiber_eq_zero h
  obtain ⟨f₁, f₂, rfl, hf₂, hf₁, hff⟩ := exists_eq_add_expect_fiber_eq_zero f
  rw [hf] at hf₁
  rw [hhh, hff, ← Real.sq_sqrt (expect_nonneg fun v _ ↦ sq_nonneg (h₁ v)),
    ← Real.sq_sqrt (expect_nonneg fun p _ ↦ sq_nonneg (h₂ p)),
    ← Real.sq_sqrt (expect_nonneg fun v _ ↦ sq_nonneg (f₁ v)),
    ← Real.sq_sqrt (expect_nonneg fun p _ ↦ sq_nonneg (f₂ p))]
  refine le_trans ?_ (add_mul_le_mul_sqrt_mul_sqrt hμ hν (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [expect_mul_walk_zigzag_eq]
  simp only [add_mul]
  simp only [mul_add, expect_add_distrib]
  rw [← add_assoc]
  -- the walk on the clouds shrinks the parts of average zero over the clouds by `λ(H)`
  have hqh := sqrt_le_mul_sqrt hν (H.expect_walk_loops_tensor_sq_le hh₂)
  have hqf := sqrt_le_mul_sqrt hν (H.expect_walk_loops_tensor_sq_le hf₂)
  gcongr ?_ + ?_ + ?_ + ?_
  · exact G.expect_mul_comp_rot_le h₁ hf₁
  · refine (expect_mul_le_sqrt_mul_sqrt univ _ _).trans ?_
    rw [expect_comp_fst (fun v ↦ h₁ v ^ 2),
      expect_comp_rot G (fun p ↦ ((loops V Unit).tensor H).walk f₂ p ^ 2)]
    exact mul_le_mul_of_nonneg_left hqf (by positivity)
  · refine (expect_mul_le_sqrt_mul_sqrt univ _ _).trans ?_
    rw [expect_comp_rot G (fun p ↦ f₁ p.1 ^ 2), expect_comp_fst (fun v ↦ f₁ v ^ 2)]
    exact mul_le_mul_of_nonneg_right hqh (by positivity)
  · refine (expect_mul_le_sqrt_mul_sqrt univ _ _).trans ?_
    rw [expect_comp_rot G (fun p ↦ ((loops V Unit).tensor H).walk f₂ p ^ 2)]
    exact mul_le_mul hqh hqf (by positivity) (by positivity)

/-- The second zig-zag estimate in bilinear form:
`𝔼 h · W f ≤ (1 - (1 - λ(G)) (1 - λ(H))²) ‖h‖ ‖f‖` for `f` of expectation zero. -/
private theorem expect_mul_walk_zigzag_le_one_sub [Nonempty D] [Nonempty E] (h : V × D → ℝ)
    {f : V × D → ℝ} (hf : 𝔼 p, f p = 0) :
    𝔼 p, h p * (G.zigzag H).walk f p ≤
      (1 - (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2) *
        (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  have hν₁ : 0 ≤ 1 - H.spectralExpansion := sub_nonneg.2 H.spectralExpansion_le_one
  obtain ⟨h₁, h₂, rfl, hh₂, -, hhh⟩ := exists_eq_add_expect_fiber_eq_zero h
  obtain ⟨f₁, f₂, rfl, hf₂, hf₁, hff⟩ := exists_eq_add_expect_fiber_eq_zero f
  rw [hf] at hf₁
  rw [expect_mul_walk_zigzag_eq, hhh, hff]
  -- `B̃ h = (1 - λ(H)) h₁ + u` with `‖u‖ ≤ λ(H) ‖h‖`, and the same for `f`
  set u : V × D → ℝ := fun p ↦ H.spectralExpansion * h₁ p.1 + ((loops V Unit).tensor H).walk h₂ p
  set w : V × D → ℝ := fun p ↦ H.spectralExpansion * f₁ p.1 + ((loops V Unit).tensor H).walk f₂ p
  have hsplit (p : V × D) :
      (h₁ p.1 + ((loops V Unit).tensor H).walk h₂ p) *
          (f₁ (G.rot p).1 + ((loops V Unit).tensor H).walk f₂ (G.rot p)) =
        (1 - H.spectralExpansion) ^ 2 * (h₁ p.1 * f₁ (G.rot p).1) +
          (1 - H.spectralExpansion) * (h₁ p.1 * w (G.rot p)) +
          (1 - H.spectralExpansion) * (u p * f₁ (G.rot p).1) + u p * w (G.rot p) := by
    simp only [u, w]
    ring
  simp only [hsplit, expect_add_distrib, ← mul_expect]
  have hu := H.sqrt_expect_mul_add_walk_loops_tensor_sq_le h₁ hh₂
  have hu' := H.sqrt_expect_mul_add_walk_loops_tensor_sq_le f₁ hf₂
  have ha : √(𝔼 v, h₁ v ^ 2) ≤ √(𝔼 v, h₁ v ^ 2 + 𝔼 p, h₂ p ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (expect_nonneg fun p _ ↦ sq_nonneg (h₂ p)))
  have hb : √(𝔼 v, f₁ v ^ 2) ≤ √(𝔼 v, f₁ v ^ 2 + 𝔼 p, f₂ p ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (expect_nonneg fun p _ ↦ sq_nonneg (f₂ p)))
  refine le_trans ?_ (mul_add_le_one_sub_mul hμ hν H.spectralExpansion_le_one
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ha hb)
  gcongr _ * ?_ + _ * ?_ + _ * ?_ + ?_
  · exact G.expect_mul_comp_rot_le h₁ hf₁
  · refine (expect_mul_le_sqrt_mul_sqrt univ _ _).trans ?_
    rw [expect_comp_fst (fun v ↦ h₁ v ^ 2), expect_comp_rot G (fun p ↦ w p ^ 2)]
    exact mul_le_mul_of_nonneg_left hu' (by positivity)
  · refine (expect_mul_le_sqrt_mul_sqrt univ _ _).trans ?_
    rw [expect_comp_rot G (fun p ↦ f₁ p.1 ^ 2), expect_comp_fst (fun v ↦ f₁ v ^ 2)]
    exact mul_le_mul_of_nonneg_right hu (by positivity)
  · refine (expect_mul_le_sqrt_mul_sqrt univ _ _).trans ?_
    rw [expect_comp_rot G (fun p ↦ w p ^ 2)]
    exact mul_le_mul hu hu' (by positivity) (by positivity)

/-- To bound `λ(G ⓩ H)` by `c ≥ 0`, it suffices to bound `𝔼 h · W f` by `c ‖h‖ ‖f‖` for every `h`
and every `f` of expectation zero, when `D` and `E` are nonempty. -/
private theorem spectralExpansion_zigzag_le_of_expect_mul_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ [Nonempty D] [Nonempty E] (h f : V × D → ℝ), 𝔼 p, f p = 0 →
      𝔼 p, h p * (G.zigzag H).walk f p ≤ c * (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2))) :
    (G.zigzag H).spectralExpansion ≤ c := by
  refine spectralExpansion_le hc fun f hf ↦ ?_
  rcases isEmpty_or_nonempty E with hE | hE
  · have : (G.zigzag H).walk f = 0 := funext fun p ↦ by simp [walk_apply]
    rw [this]
    simpa using mul_nonneg (sq_nonneg c) (expect_nonneg fun p _ ↦ sq_nonneg (f p))
  rcases isEmpty_or_nonempty D with hD | hD
  · simp
  exact expect_sq_le_of_expect_mul_le (h _ f hf)

/-- **The zig-zag theorem**
[Reingold, Vadhan and Wigderson, Theorem 3.2][ReingoldVadhanWigderson2002]
[Hoory, Linial and Wigderson, Section 9.3][HooryLinialWigderson2006]: the spectral expansion of
`G ⓩ H` is at most `λ(G) + λ(H) + λ(H) ^ 2`. -/
theorem spectralExpansion_zigzag_le :
    (G.zigzag H).spectralExpansion ≤
      G.spectralExpansion + H.spectralExpansion + H.spectralExpansion ^ 2 := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  exact G.spectralExpansion_zigzag_le_of_expect_mul_le H (by positivity) fun h _ hf ↦
    G.expect_mul_walk_zigzag_le H h hf

/-- The spectral expansion of `G ⓩ H` is at most `1 - (1 - λ(G)) (1 - λ(H)) ^ 2`: the zig-zag
product of two expanders is an expander. This form of the bound is useful when `λ(G)` and
`λ(H)` are close to `1`. -/
theorem spectralExpansion_zigzag_le_one_sub :
    (G.zigzag H).spectralExpansion ≤
      1 - (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2 := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  have hμ₁ := G.spectralExpansion_le_one
  have hν₁ := H.spectralExpansion_le_one
  refine G.spectralExpansion_zigzag_le_of_expect_mul_le H ?_ fun h _ hf ↦
    G.expect_mul_walk_zigzag_le_one_sub H h hf
  have : (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2 ≤ 1 :=
    (mul_le_mul (by linarith) (pow_le_one₀ (by linarith) (by linarith)) (sq_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  linarith

/-- The zig-zag product of two graphs of spectral expansion less than `1` has spectral expansion
less than `1` [Reingold, Vadhan and Wigderson, Theorem 3.2][ReingoldVadhanWigderson2002]. -/
theorem spectralExpansion_zigzag_lt_one (hG : G.spectralExpansion < 1)
    (hH : H.spectralExpansion < 1) : (G.zigzag H).spectralExpansion < 1 :=
  (G.spectralExpansion_zigzag_le_one_sub H).trans_lt
    (sub_lt_self 1 (mul_pos (sub_pos.2 hG) (pow_pos (sub_pos.2 hH) 2)))

end Cslib.RotationMap
