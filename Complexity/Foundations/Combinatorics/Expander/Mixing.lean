/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Basic
public import Mathlib.Analysis.Real.Sqrt
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The expander mixing lemma

On a regular graph of small spectral expansion `λ(G)`, edges are spread out as in a random graph:
the number of edges between two sets of vertices is close to what a random graph of the same
density would have.

For real functions on the vertices, with expectations taken over uniform vertices, the correlation
of `f` at the start of a walk of length `t` with `g` at its end is the product of the expectations
up to `λ(G) ^ t` times the two standard deviations (`sq_expect_mul_walk_pow_sub_le`). Applied to the
indicator functions of two sets `S` and `T` of vertices, this is the **expander mixing lemma**
[Arora and Barak, Section 21.2][AroraBarak09]
[Hoory, Linial and Wigderson, Lemma 2.5][HooryLinialWigderson2006], in the sharper form

`|e(S, T) - d |S| |T| / n| ≤ λ(G) d √(|S| |Sᶜ| |T| |Tᶜ|) / n`

(`abs_card_interedges_sub_le`), for a `d`-regular graph on `n` vertices, where `e(S, T)` counts
the edges from `S` to `T` with those inside `S ∩ T` counted twice.

For `T = Sᶜ` a one-sided bound suffices: at least `(1 - μ) d |S| |Sᶜ| / n` edges leave `S` as soon
as `𝔼 f · G.walk f ≤ μ 𝔼 f²` for all `f` of expectation zero
(`le_card_interedges_compl_of_expect_mul_walk_le`). This is the easy half of the discrete Cheeger
inequality [Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]; with `μ = λ(G)` it
says that spectral expanders are edge expanders [Arora and Barak, Section 21.2][AroraBarak09]
(`le_card_interedges_compl`, `le_card_interedges_compl_of_two_mul_card_le`).

## Main results

* `Cslib.RotationMap.expect_mul_walk_pow_eq`: the correlation along a walk is the product of the
  expectations plus the correlation of the centered functions.
* `Cslib.RotationMap.sq_expect_mul_walk_pow_sub_le`: the mixing lemma for functions and walks of
  any length.
* `Cslib.RotationMap.abs_card_interedges_sub_le`,
  `Cslib.RotationMap.abs_card_interedges_sub_le_mul_sqrt`: the expander mixing lemma.
* `Cslib.RotationMap.le_card_interedges_compl_of_expect_mul_walk_le`,
  `Cslib.RotationMap.le_card_interedges_compl`: edge expansion from a spectral bound.
* `Cslib.RotationMap.le_card_interedges_compl_of_two_mul_card_le`: a set of at most half of the
  vertices has at least `(1 - λ(G)) d |S| / 2` edges leaving it.
* `Cslib.RotationMap.mul_card_filter_ne_le_card_filter_ne_neighbor`: an expander has many edges
  between differently labelled vertices.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*} [Fintype V] [Fintype D] (G : RotationMap V D)

/-- Centering a function leaves an expectation of zero. -/
private theorem expect_sub_expect (f : V → ℝ) : 𝔼 v, (f v - 𝔼 w, f w) = 0 :=
  Fintype.expect_balance f

/-- The second moment of the centered function is the variance. -/
private theorem expect_sub_expect_sq (f : V → ℝ) :
    𝔼 v, (f v - 𝔼 w, f w) ^ 2 = 𝔼 v, f v ^ 2 - (𝔼 v, f v) ^ 2 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  · simp only [sub_sq, expect_add_distrib, expect_sub_distrib, ← expect_mul, ← mul_expect,
      Fintype.expect_const]
    ring

section Mixing

variable [Nonempty D]

/-- The correlation of `f` with `g` along walks of length `t` is the product of the expectations
plus the correlation of the centered functions. -/
theorem expect_mul_walk_pow_eq (t : ℕ) (f g : V → ℝ) :
    𝔼 v, f v * (G.walk ^ t) g v =
      (𝔼 v, f v) * 𝔼 v, g v +
        𝔼 v, (f v - 𝔼 w, f w) * (G.walk ^ t) (fun w ↦ g w - 𝔼 u, g u) v := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  have hg : (G.walk ^ t) (fun w ↦ g w - 𝔼 u, g u) = fun v ↦ (G.walk ^ t) g v - 𝔼 u, g u := by
    rw [show (fun w ↦ g w - 𝔼 u, g u) = g - fun _ ↦ 𝔼 u, g u from rfl, map_sub, walk_pow_const]
    rfl
  simp only [hg, sub_mul, mul_sub, expect_sub_distrib, ← expect_mul, ← mul_expect, expect_walk_pow,
    Fintype.expect_const]
  ring

/-- **The mixing lemma for functions**: the correlation `𝔼 v, f v * (G.walk ^ t) g v` of `f` with
`g` along walks of length `t` differs from the product of their expectations by at most
`λ(G) ^ t` times their standard deviations. Squared: the square of the difference is at most
`λ(G) ^ (2 t)` times the product of the variances `𝔼 f² - (𝔼 f)²` and `𝔼 g² - (𝔼 g)²`. -/
theorem sq_expect_mul_walk_pow_sub_le (t : ℕ) (f g : V → ℝ) :
    (𝔼 v, f v * (G.walk ^ t) g v - (𝔼 v, f v) * 𝔼 v, g v) ^ 2 ≤
      G.spectralExpansion ^ (2 * t) * (𝔼 v, f v ^ 2 - (𝔼 v, f v) ^ 2) *
        (𝔼 v, g v ^ 2 - (𝔼 v, g v) ^ 2) := by
  rw [G.expect_mul_walk_pow_eq, add_sub_cancel_left, ← expect_sub_expect_sq,
    ← expect_sub_expect_sq]
  calc
    _ ≤ (𝔼 v, (f v - 𝔼 w, f w) ^ 2) *
          𝔼 v, (G.walk ^ t) (fun w ↦ g w - 𝔼 u, g u) v ^ 2 :=
      expect_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (𝔼 v, (f v - 𝔼 w, f w) ^ 2) *
          (G.spectralExpansion ^ (2 * t) * 𝔼 v, (g v - 𝔼 w, g w) ^ 2) := by
      gcongr
      exact G.expect_walk_pow_sq_le_spectralExpansion_pow_mul (expect_sub_expect g) t
    _ = _ := by ring

end Mixing

section Sets

variable [DecidableEq V]

/-- The correlation of the indicator function of `S` with the walk operator applied to that of `T`
is the proportion of the darts from `S` to `T`. -/
private theorem expect_boole_mem_mul_walk (S T : Finset V) :
    𝔼 v, (if v ∈ S then (1 : ℝ) else 0) * G.walk (fun w ↦ if w ∈ T then 1 else 0) v =
      #(G.interedges S T) / (Fintype.card V * Fintype.card D) := by
  simp only [walk_apply, mul_expect]
  rw [← expect_product', univ_product_univ, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
    Nat.cast_mul]
  simp only [ite_zero_mul_ite_zero, mul_one, sum_boole]
  congr 3
  ext p
  simp

/-- The number of vertices outside `S`. -/
private theorem card_compl_eq (S : Finset V) : (#Sᶜ : ℝ) = Fintype.card V - #S := by
  rw [eq_sub_iff_add_eq, ← Nat.cast_add, card_compl_add_card]

/-- **The expander mixing lemma** [Arora and Barak, Section 21.2][AroraBarak09]
[Hoory, Linial and Wigderson, Lemma 2.5][HooryLinialWigderson2006], sharper form: in a `d`-regular
graph on `n` vertices, the number of edges from `S` to `T` differs from `d |S| |T| / n` by at most
`λ(G) d √(|S| |Sᶜ| |T| |Tᶜ|) / n`. -/
theorem abs_card_interedges_sub_le (S T : Finset V) :
    |(#(G.interedges S T) : ℝ) - Fintype.card D * #S * #T / Fintype.card V| ≤
      G.spectralExpansion * Fintype.card D * √((#S : ℝ) * #Sᶜ * #T * #Tᶜ) /
        Fintype.card V := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simp [interedges]
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hV
    simp [Subsingleton.elim S ∅]
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 hV
  have hd : (0 : ℝ) < Fintype.card D := Nat.cast_pos.2 Fintype.card_pos
  have h := G.sq_expect_mul_walk_pow_sub_le 1 (fun v ↦ if v ∈ S then 1 else 0)
    (fun v ↦ if v ∈ T then 1 else 0)
  rw [pow_one, mul_one, expect_boole_mem_mul_walk, Fintype.expect_boole_mem,
    Fintype.expect_boole_mem, Fintype.expect_boole_mem_sq, Fintype.expect_boole_mem_sq,
    nnratCast_dens, nnratCast_dens] at h
  have := G.spectralExpansion_nonneg
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), card_compl_eq, card_compl_eq]
  generalize (#(G.interedges S T) : ℝ) = e at h ⊢
  generalize (#S : ℝ) = s at h ⊢
  generalize (#T : ℝ) = t at h ⊢
  generalize (Fintype.card V : ℝ) = n at h hn ⊢
  generalize (Fintype.card D : ℝ) = d at h hd ⊢
  calc
    _ = (n * d) ^ 2 * (e / (n * d) - s / n * (t / n)) ^ 2 := by field_simp
    _ ≤ (n * d) ^ 2 *
          (G.spectralExpansion ^ 2 * (s / n - (s / n) ^ 2) * (t / n - (t / n) ^ 2)) := by gcongr
    _ = _ := by field_simp

/-- **The expander mixing lemma** in its usual form [Arora and Barak, Section 21.2][AroraBarak09]
[Hoory, Linial and Wigderson, Lemma 2.5][HooryLinialWigderson2006]: in a `d`-regular graph on `n`
vertices, the number of edges from `S` to `T` differs from `d |S| |T| / n` by at most
`λ(G) d √(|S| |T|)`. -/
theorem abs_card_interedges_sub_le_mul_sqrt (S T : Finset V) :
    |(#(G.interedges S T) : ℝ) - Fintype.card D * #S * #T / Fintype.card V| ≤
      G.spectralExpansion * Fintype.card D * √((#S : ℝ) * #T) := by
  refine (G.abs_card_interedges_sub_le S T).trans ?_
  have := G.spectralExpansion_nonneg
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · rw [hV, Nat.cast_zero, div_zero]
    positivity
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 hV
  rw [div_le_iff₀ hn, mul_assoc _ (√_), ← Real.sqrt_sq hn.le, ← Real.sqrt_mul (by positivity)]
  gcongr _ * √?_
  have hS : (#Sᶜ : ℝ) ≤ Fintype.card V := Nat.cast_le.2 (card_le_univ _)
  have hT : (#Tᶜ : ℝ) ≤ Fintype.card V := Nat.cast_le.2 (card_le_univ _)
  calc (#S : ℝ) * #Sᶜ * #T * #Tᶜ = #S * #T * (#Sᶜ * #Tᶜ) := by ring
    _ ≤ #S * #T * (Fintype.card V * Fintype.card V) := by gcongr
    _ = #S * #T * Fintype.card V ^ 2 := by ring

/-- **Edge expansion from a one-sided spectral bound**: if `𝔼 v, f v * G.walk f v ≤ μ 𝔼 f²` for
every function `f` of expectation zero, then in a `d`-regular graph on `n` vertices at least
`(1 - μ) d |S| |Sᶜ| / n` edges leave `S`. The best such `μ` is the second largest eigenvalue of the
walk operator, so this is the easy half of the discrete Cheeger inequality
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]. -/
theorem le_card_interedges_compl_of_expect_mul_walk_le {μ : ℝ}
    (hμ : ∀ f : V → ℝ, 𝔼 v, f v = 0 → 𝔼 v, f v * G.walk f v ≤ μ * 𝔼 v, f v ^ 2)
    (S : Finset V) :
    (1 - μ) * Fintype.card D * #S * #Sᶜ / Fintype.card V ≤ #(G.interedges S Sᶜ) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simp
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · rw [hV, Nat.cast_zero, div_zero]
    positivity
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 hV
  have hd : (0 : ℝ) < Fintype.card D := Nat.cast_pos.2 Fintype.card_pos
  have h := hμ _ (expect_sub_expect fun v ↦ if v ∈ S then 1 else 0)
  have hc := G.expect_mul_walk_pow_eq 1 (fun v ↦ if v ∈ S then 1 else 0)
    (fun v ↦ if v ∈ S then 1 else 0)
  rw [pow_one] at hc
  rw [← add_sub_cancel_left ((𝔼 v, if v ∈ S then (1 : ℝ) else 0) * 𝔼 v, if v ∈ S then 1 else 0)
    (𝔼 v, _ * G.walk _ v), ← hc, expect_sub_expect_sq, expect_boole_mem_mul_walk,
    Fintype.expect_boole_mem, Fintype.expect_boole_mem_sq, nnratCast_dens] at h
  have he : (#(G.interedges S S) : ℝ) + #(G.interedges S Sᶜ) = #S * Fintype.card D := by
    exact_mod_cast G.card_interedges_add_card_interedges_compl S S
  rw [card_compl_eq, div_le_iff₀ hn]
  generalize (#(G.interedges S S) : ℝ) = e₁ at h he
  generalize (#(G.interedges S Sᶜ) : ℝ) = e₂ at he ⊢
  generalize (#S : ℝ) = s at h he ⊢
  generalize (Fintype.card V : ℝ) = n at h hn ⊢
  generalize (Fintype.card D : ℝ) = d at h hd he ⊢
  have h' : e₁ * n - s ^ 2 * d ≤ μ * d * (s * n - s ^ 2) := by
    have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ n ^ 2 * d)
    field_simp at this
    linarith
  nlinarith

/-- **Spectral expanders are edge expanders** [Arora and Barak, Section 21.2][AroraBarak09]: in a
`d`-regular graph on `n` vertices, at least `(1 - λ(G)) d |S| |Sᶜ| / n` edges leave `S`. -/
theorem le_card_interedges_compl (S : Finset V) :
    (1 - G.spectralExpansion) * Fintype.card D * #S * #Sᶜ / Fintype.card V ≤
      #(G.interedges S Sᶜ) :=
  G.le_card_interedges_compl_of_expect_mul_walk_le
    (fun _ hf ↦ (le_abs_self _).trans (G.abs_expect_mul_walk_le hf)) S

/-- **Spectral expanders are edge expanders** [Arora and Barak, Section 21.2][AroraBarak09]: in a
`d`-regular graph, at least `(1 - λ(G)) d |S| / 2` edges leave a set `S` of at most half of the
vertices. -/
theorem le_card_interedges_compl_of_two_mul_card_le {S : Finset V}
    (hS : 2 * #S ≤ Fintype.card V) :
    (1 - G.spectralExpansion) * Fintype.card D * #S / 2 ≤ #(G.interedges S Sᶜ) := by
  refine le_trans ?_ (G.le_card_interedges_compl S)
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hV
    simp [Subsingleton.elim S ∅]
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 hV
  have hA : 0 ≤ (1 - G.spectralExpansion) * Fintype.card D * #S :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 G.spectralExpansion_le_one) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hc : (Fintype.card V : ℝ) ≤ 2 * #Sᶜ := by
    rw [card_compl_eq]
    have : (2 * #S : ℝ) ≤ Fintype.card V := by exact_mod_cast hS
    linarith
  rw [div_le_div_iff₀ two_pos hn]
  nlinarith [mul_le_mul_of_nonneg_left hc hA]

end Sets

open Classical in
/-- The number of darts `(v, i)` whose endpoints have different `f`-labels, sorted by the label of
their first end, equals the sum over `a ∈ univ.image f` of the number of edges leaving
`{v | f v = a}`. -/
private theorem card_filter_ne_neighbor_eq_sum_card_interedges {α : Type*} [DecidableEq α]
    (f : V → α) :
    (#{p : V × D | f p.1 ≠ f (G.neighbor p.1 p.2)} : ℝ) =
      ∑ a ∈ univ.image f, (#(G.interedges {v | f v = a} ({v | f v = a} : Finset V)ᶜ) : ℝ) := by
  rw [card_eq_sum_card_fiberwise (f := fun p : V × D ↦ f p.1) (t := univ.image f)
    fun p _ ↦ mem_image_of_mem f (mem_univ _)]
  push_cast
  refine sum_congr rfl fun a _ ↦ ?_
  congr 2
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_interedges, mem_compl]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨rfl, fun h' ↦ h h'.symm⟩
  · rintro ⟨rfl, h⟩
    exact ⟨fun h' ↦ h h'.symm, rfl⟩

/-- **Disagreement across an expander, for a most frequent label**: if no label is taken by more
vertices than `c`, at least `(1 - λ(G)) d |{f ≠ c}|` darts join two differently labelled vertices,
whatever the number of labels. The darts leaving the set of the vertices labelled `a` number at
least `(1 - λ(G)) d |{f = a}| |{f ≠ a}| / n`, and `|{f ≠ a}| ≥ |{f ≠ c}|` for every label `a`. -/
theorem mul_card_filter_ne_le_card_filter_ne_neighbor {α : Type*} [DecidableEq α] (f : V → α)
    {c : α} (hc : ∀ a, #{v | f v = a} ≤ #{v | f v = c}) :
    (1 - G.spectralExpansion) * Fintype.card D * #{v | f v ≠ c} ≤
      #{p : V × D | f p.1 ≠ f (G.neighbor p.1 p.2)} := by
  classical
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hV
    simp
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 hV
  have hlam : 0 ≤ (1 - G.spectralExpansion) * Fintype.card D :=
    mul_nonneg (sub_nonneg.2 G.spectralExpansion_le_one) (Nat.cast_nonneg _)
  set T := univ.image f
  set s : α → ℝ := fun a ↦ #{v | f v = a}
  -- the vertices, sorted by their labels
  have hs : ∑ a ∈ T, s a = Fintype.card V := by
    simp only [s]
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise fun v _ ↦ mem_image_of_mem f (mem_univ v),
      card_univ]
  have hne : (#{v | f v ≠ c} : ℝ) = Fintype.card V - s c := by
    rw [← card_compl_eq]
    congr 2
    ext v
    simp
  have hterm (a : α) : (1 - G.spectralExpansion) * Fintype.card D * s a *
      (Fintype.card V - s a) / Fintype.card V ≤
        #(G.interedges {v | f v = a} ({v | f v = a} : Finset V)ᶜ) := by
    have h := G.le_card_interedges_compl {v | f v = a}
    rwa [card_compl_eq] at h
  have hsc (a : α) : s a ≤ s c := by simp only [s]; exact_mod_cast hc a
  rw [hne, G.card_filter_ne_neighbor_eq_sum_card_interedges f]
  calc (1 - G.spectralExpansion) * Fintype.card D * (Fintype.card V - s c)
      = ∑ a ∈ T, (1 - G.spectralExpansion) * Fintype.card D * s a * (Fintype.card V - s c) /
          Fintype.card V := by
        rw [← sum_div, ← sum_mul, ← mul_sum, hs]
        field_simp
    _ ≤ ∑ a ∈ T, (1 - G.spectralExpansion) * Fintype.card D * s a * (Fintype.card V - s a) /
          Fintype.card V := by
        gcongr with a
        exact hsc a
    _ ≤ _ := sum_le_sum fun a _ ↦ hterm a

end Cslib.RotationMap
