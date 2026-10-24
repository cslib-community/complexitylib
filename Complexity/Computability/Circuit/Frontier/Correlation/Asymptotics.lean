/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Correlation.Circuit
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exponentially small correlation below `(1 + 1/(2A)) n` gates

Let every set of `⌊n/2⌋` coordinates have cut rank at least `⌊n/2⌋ - τ n` in the polar matrix of a
quadratic form `S_n` over `𝔽₂`, and let subcubic graphs have layouts of width
`(A + o(1)) β₁ + o(|V|)` (`LayoutBound 3 A`). Balance the two finite bounds of
`Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_unread` and
`Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_layout` at `θ n` unread inputs, where
`θ = (1/2 - A (c - 1)) / (1 + A)`:

* with at least `θ n` unread inputs, `correlation² ≤ 2^{-(θ - τ) n + O(1)}`;
* with fewer, the graph of a circuit of fan-in two with at most `c n` inner gates has cycle rank at
  most `(c - 1 + θ) n + 1` (`Compiler.cycleRank_add_ncard_read_le`), hence a layout of width about
  `A (c - 1 + θ) n`, and the frontier bound gives the same exponent, since
  `A (c - 1 + θ) - 1/2 = -θ`.

So the correlation is `2^{-γ n}` for every `γ < (θ - τ)/2 = (c* - c)/(2L) - τ/2`, where
`c* = 1 + 1/(2A)` and `L = 1 + 1/A` (`eventually_abs_correlation_quadForm_le`), and for every
`γ < (c* - c)/(2L)` when the deficiency is `o(n)`
(`eventually_abs_correlation_quadForm_le_of_isLittleO`). Note `c* = (1 + L)/2`: the threshold is
halfway between `1` and the coefficient `L` of the worst-case frontier lower bound
(`Cslib.Circuits.Frontier.circuitLowerBound_of_layoutBound`).

## Main results

* `Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le`: correlation `2^{-γ n}` for every
  `γ < (c* - c)/(2L) - τ/2`.
* `Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_of_isLittleO`: correlation
  `2^{-γ n}` for every `γ < (c* - c)/(2L)`, for a sublinear deficiency.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Matrix

universe v

/-- From a squared bound to an absolute bound with half the exponent. -/
private theorem abs_le_two_rpow_of_sq_le {y γ : ℝ} {n : ℕ}
    (h : y ^ 2 ≤ (2 : ℝ) ^ (-(2 * γ) * n)) : |y| ≤ (2 : ℝ) ^ (-γ * n) := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have hsq : ((2 : ℝ) ^ (-γ * n)) ^ 2 = (2 : ℝ) ^ (-(2 * γ) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast
    ring_nf
  rwa [hsq]

/-- The rate in two forms: `2 (c* - c)/(2L) = (1/2 - A (c - 1)) / (1 + A)`, where
`c* = 1 + 1/(2A)` and `L = 1 + 1/A`. -/
private theorem two_mul_rate_eq {A c : ℝ} (hA : 0 < A) :
    2 * ((1 + 1 / (2 * A) - c) / (2 * (1 + 1 / A))) = (1 / 2 - A * (c - 1)) / (1 + A) := by
  field_simp
  ring

/-- **Exponentially small correlation.** Let subcubic graphs have layouts of width
`(A + o(1)) β₁ + o(|V|)` (`LayoutBound 3 A`), and let every set of `⌊n/2⌋` coordinates have cut
rank at least `⌊n/2⌋ - τ n` in `Q_n + Q_nᵀ` for all large `n`. Then for every `c ≥ 1/2` and every
`γ < (c* - c)/(2L) - τ/2`, where `c* = 1 + 1/(2A)` and `L = 1 + 1/A`, for all large `n` every
circuit of fan-in at most two, over any basis on `Bool` and accepting any set of values, with at
most `c n` gates of positive arity has correlation at most `2^{-γ n}` in absolute value with the
quadratic form of `Q_n`. -/
theorem eventually_abs_correlation_quadForm_le {A c τ γ : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound 3 A) (hc : 1 / 2 ≤ c)
    (hγ : γ < (1 + 1 / (2 * A) - c) / (2 * (1 + 1 / A)) - τ / 2)
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + τ * n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) := by
  set θ := (1 / 2 - A * (c - 1)) / (1 + A) with hθdef
  have h2γ : 2 * γ < θ - τ := by
    rw [hθdef, ← two_mul_rate_eq hA]
    linarith
  have hθeq : A * (c - 1 + θ) - 1 / 2 = -θ := by
    rw [hθdef]
    field_simp
    ring
  have hθhalf : θ ≤ 1 / 2 := by
    rw [hθdef, div_le_iff₀ (by linarith)]
    nlinarith
  set δ := θ - τ - 2 * γ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set K := 5 * c + |θ| + 1 with hKdef
  have hK : 0 < K := by rw [hKdef]; have := abs_nonneg θ; linarith
  set η := δ / (2 * K) with hηdef
  have hη : 0 < η := by positivity
  have hηK : η * K = δ / 2 := by rw [hηdef]; field_simp
  have hηθ : η * (5 * c - 1 + θ) ≤ δ / 2 := by
    rw [← hηK]
    refine mul_le_mul_of_nonneg_left ?_ hη.le
    have := le_abs_self θ
    rw [hKdef]
    linarith
  obtain ⟨C₀, hC₀⟩ := hlayout η hη
  set R := (2 / δ) * (3 / 2 + A + 4 * η + |C₀|) with hRdef
  have hlarge : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)
  filter_upwards [hQ, hlarge] with n hQn hRn
  intro σ I Acc C hfan hsize
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hRn' : 3 / 2 + A + 4 * η + |C₀| ≤ δ / 2 * n := by
    have : δ / 2 * R = 3 / 2 + A + 4 * η + |C₀| := by rw [hRdef]; field_simp
    nlinarith
  have hC₀abs := le_abs_self C₀
  have hθn : θ * n ≤ 1 / 2 * n := mul_le_mul_of_nonneg_right hθhalf hn0
  apply abs_le_two_rpow_of_sq_le
  set N := Compiler.network C I fun _ => Acc
  set s := C.innerSize
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hcompl : (N.readᶜ.ncard : ℝ) + N.read.ncard = n := by
    rw [← Nat.cast_add, add_comm, ncard_add_ncard_compl, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hhalf' : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
    linarith
  have hhalf : ((n / 2 : ℕ) : ℝ) ≤ n / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast Nat.div_mul_le_self n 2
  by_cases hd : θ * n ≤ N.readᶜ.ncard
  · -- Many unread inputs.
    have H := sq_correlation_quadForm_le_of_unread I Acc C (Q n) hQn
      (k := min N.readᶜ.ncard (n / 2)) (min_le_right _ _) (min_le_left _ _)
    refine H.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hk : θ * n - 1 / 2 ≤ ((min N.readᶜ.ncard (n / 2) : ℕ) : ℝ) := by
      rcases min_choice N.readᶜ.ncard (n / 2) with h | h <;> rw [h] <;> linarith
    rw [hδdef] at hRn'
    nlinarith [abs_nonneg C₀]
  · -- Few unread inputs: the frontier bound.
    push Not at hd
    have hread : n / 2 ≤ N.read.ncard := by
      have : ((n / 2 : ℕ) : ℝ) < N.read.ncard := by linarith
      exact_mod_cast this.le
    have hrank : ((Compiler.graph C).cycleRank : ℝ) + N.read.ncard ≤ s + 1 := by
      have H := Compiler.cycleRank_add_ncard_read_le I (fun _ => Acc) hfan (Compiler.connected C)
      simp only [Nat.add_one_sub_one, one_mul] at H
      exact_mod_cast H
    have hV : (Nat.card (Compiler.Vertex C) : ℝ) ≤ 4 * s + 3 := by
      have H := Compiler.card_vertex_le (c := C) hfan
      have : Nat.card (Compiler.Vertex C) ≤ 4 * s + 3 := by simpa [s, mul_comm, ← mul_assoc] using H
      exact_mod_cast this
    obtain ⟨π, hπ⟩ := hC₀ _ _ (Compiler.graph C) (Compiler.connected C) Compiler.loopless
      (Compiler.maxDegreeLE le_rfl hfan)
    set B := (A + η) * (Compiler.graph C).cycleRank + η * Nat.card (Compiler.Vertex C) + C₀
    have hB : 0 ≤ B := (Nat.cast_nonneg _).trans hπ
    have hw : (Compiler.graph C).width π ≤ ⌊B⌋₊ := Nat.le_floor hπ
    have H := sq_correlation_quadForm_le_of_layout I Acc C (Q n) hQn π hw hread
    refine H.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
    have hcycle : ((Compiler.graph C).cycleRank : ℝ) ≤ (c - 1 + θ) * n + 1 := by
      have : (c - 1 + θ) * n = c * n - n + θ * n := by ring
      linarith
    have hcyc0 : (0 : ℝ) ≤ (Compiler.graph C).cycleRank := Nat.cast_nonneg _
    have hBle : B ≤ (A + η) * ((c - 1 + θ) * n + 1) + η * (4 * c * n + 3) + C₀ := by
      have h1 := mul_le_mul_of_nonneg_left hcycle (by positivity : (0 : ℝ) ≤ A + η)
      have h2 : η * (Nat.card (Compiler.Vertex C) : ℝ) ≤ η * (4 * c * n + 3) := by
        refine mul_le_mul_of_nonneg_left ?_ hη.le
        have : 4 * c * n = 4 * (c * n) := by ring
        linarith
      change (A + η) * (Compiler.graph C).cycleRank +
        η * Nat.card (Compiler.Vertex C) + C₀ ≤ _
      linarith
    have hexp : (A + η) * ((c - 1 + θ) * n + 1) + η * (4 * c * n + 3) =
        (A * (c - 1 + θ) - 1 / 2) * n + n / 2 + η * (5 * c - 1 + θ) * n + A + 4 * η := by
      ring
    rw [hθeq] at hexp
    have hηθn := mul_le_mul_of_nonneg_right hηθ hn0
    rw [hδdef] at hRn' hηθn
    linarith

/-- **Exponentially small correlation, sublinear deficiency.** Under `LayoutBound 3 A`, if every
set of `⌊n/2⌋` coordinates has cut rank at least `⌊n/2⌋ - o(n)` in `Q_n + Q_nᵀ`, then for every
`c ≥ 1/2` and every `γ < (c* - c)/(2L)`, where `c* = 1 + 1/(2A)` and `L = 1 + 1/A`, for all large
`n` every circuit of fan-in at most two with at most `c n` gates of positive arity has correlation
at most `2^{-γ n}` in absolute value with the quadratic form of `Q_n`. -/
theorem eventually_abs_correlation_quadForm_le_of_isLittleO {A c γ : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound 3 A) (hc : 1 / 2 ≤ c)
    (hγ : γ < (1 + 1 / (2 * A) - c) / (2 * (1 + 1 / A)))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) := by
  set τ := (1 + 1 / (2 * A) - c) / (2 * (1 + 1 / A)) - γ with hτ
  have hτpos : 0 < τ := by rw [hτ]; linarith
  refine eventually_abs_correlation_quadForm_le hA hlayout hc (τ := τ) (by rw [hτ]; linarith)
    Q ?_
  filter_upwards [hQ, he.bound hτpos] with n hQn hen U hU
  have h₁ := hQn U hU
  have h₂ : e n ≤ τ * n := by
    have := le_abs_self (e n)
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hen
    linarith
  linarith

end Cslib.Circuits.Frontier
