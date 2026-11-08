/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Boolean.Counting
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Data.Nat.Dist
public import Mathlib.InformationTheory.Hamming
import Complexity.Computability.Circuit.Boolean.Correction
import Complexity.Computability.Circuit.Boolean.SparseSynthesisConstruction
import Complexity.Computability.Circuit.Complexity
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sparse synthesis and the square-root continuity of circuit complexity

Consider Boolean functions on `n = 2 p` inputs, and sets of at most `2 ^ p` inputs, the square
root of the number of all inputs. For every `ε > 0` and all large `p`:

* the indicator of such a set has a De Morgan circuit with at most `(1 + ε) 2 ^ p` gates
  (`complexity_indicator_le`), the case `N = 2 ^ p` of Lupanov's bound for functions with `N`
  ones [Lupanov1965], [Chashkin, Theorem 3.1][Chashkin2024];
* every function on such a set agrees there with a De Morgan circuit with at most
  `(1 + ε) 2 ^ p / p` gates (`complexityOn_le`), the case `D = 2 ^ p` of Sholomov's bound
  `D / log₂ D` for functions defined on `D` inputs [Sholomov1969],
  [Chashkin, Theorem 2.1][Chashkin2024].

Both bounds are asymptotically optimal [Chashkin, Section 1][Chashkin2024]. Chashkin states them
for circuits over all binary operations; the constructions spend their leading gates on
disjunctions, and the bounds are proved here for De Morgan circuits. The circuits are those of
`Complexity.Computability.Circuit.Boolean.SparseSynthesisConstruction`; this file chooses their
parameters, uniformly in the set and the function.

Together with the sparse corrections of `Complexity.Computability.Circuit.Boolean.Correction`,
these bounds show that circuit complexity is continuous at the scale of the square root of the
number of inputs: changing a function with any number of outputs on at most `2 ^ p` inputs, and in
at most `2 p` outputs, changes its complexity by at most `(3 + ε) 2 ^ p` (`dist_complexity_le`).
Indeed the indicator of the changed inputs costs `(1 + ε) 2 ^ p`, and each of the at most `2 p`
changed outputs costs `(1 + ε) 2 ^ p / p` on those inputs. For a single output the bound is
`(1 + ε) 2 ^ p` (`dist_complexity_single_le`). The order is optimal: for `p ≥ 4`, by counting,
some set of `2 ^ p` inputs has an indicator of complexity more than `2 ^ p / 16`
(`exists_hard_indicator`), so no continuity bound is `o(2 ^ p)`
(`not_isLittleO_of_dist_complexity_le`). Consequences are that exact hardness survives sparse
errors (`lt_hammingDist_of_complexity_add_lt`, `dist_complexity_isLittleO`), and that circuits of
`(1 + ε) 2 ^ p / p` gates shatter every set of at most `2 ^ p` inputs (`shatters_circuitSets`).

The circuit model counts every AND, OR, NOT and constant gate; fan-out and output wires are free.

## Main definitions

* `Cslib.Circuits.Boolean.SparseSynthesis.circuitSets`: the sets whose indicators have circuits
  with at most `s` gates.

## Main results

* `Cslib.Circuits.Boolean.SparseSynthesis.complexity_indicator_le`: sparse indicators.
* `Cslib.Circuits.Boolean.SparseSynthesis.complexityOn_le`: partial functions.
* `Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_le`: square-root continuity.
* `Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_single_le`: square-root continuity for
  a single output.
* `Cslib.Circuits.Boolean.SparseSynthesis.exists_hard_indicator`,
  `Cslib.Circuits.Boolean.SparseSynthesis.not_isLittleO_of_dist_complexity_le`: optimality.
* `Cslib.Circuits.Boolean.SparseSynthesis.lt_hammingDist_of_complexity_add_lt`,
  `Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_isLittleO`: hardness survives sparse
  errors.
* `Cslib.Circuits.Boolean.SparseSynthesis.shatters_circuitSets`,
  `Cslib.Circuits.Boolean.SparseSynthesis.le_vcDim_circuitSets`: small circuits shatter
  square-root-sized samples.

## References

* [A. V. Chashkin, *On computing partial Boolean functions*][Chashkin2024]
* [O. B. Lupanov, *On an approach to the synthesis of control systems: the principle of local
  coding*][Lupanov1965]
* [L. A. Sholomov, *On the realization of incompletely defined Boolean functions by circuits of
  functional elements*][Sholomov1969]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SparseSynthesis

open Filter Finset

/-! ### Estimates -/

/-- `2 ^ k + 1 ≤ 2 ^ (k + 1)`. -/
private theorem two_pow_add_one_le (k : ℕ) : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
  have := Nat.one_le_two_pow (n := k)
  rw [pow_succ]
  omega

/-- `2 ^ (2 p) / 2 ^ e ≤ 2 ^ (p - h)` when `p + h ≤ e`. -/
private theorem two_pow_div_le {p h e : ℕ} (hh : h ≤ p) (he : p + h ≤ e) :
    2 ^ (2 * p) / 2 ^ e ≤ 2 ^ (p - h) :=
  calc 2 ^ (2 * p) / 2 ^ e ≤ 2 ^ (2 * p) / 2 ^ (p + h) :=
        Nat.div_le_div_left (Nat.pow_le_pow_right two_pos he) (Nat.two_pow_pos _)
    _ = 2 ^ (p - h) := by rw [Nat.pow_div (by omega) two_pos]; congr 1; omega

/-- The sparse indicator construction on `2 p` inputs costs at most its leading term
`t ⌊2 ^ p / K⌋` plus `32 (p + 1) ^ 3 2 ^ (p - h)`, when the tables and the residual inputs fit in
`p - h` bits. -/
private theorem indicatorBound_le {p h k l K a t : ℕ} (hh : h ≤ p) (hk : k ≤ p - h)
    (hl : l ≤ p - h) (hkl : k + l ≤ 2 * p) (hK : (k + 1) * K ≤ p - h) (hKp : K ≤ p)
    (ht : t ≤ p + 1) (hat : p + h ≤ a * t) :
    indicatorBound (2 * p) k l K p a t ≤ t * (2 ^ p / K) + 32 * (p + 1) ^ 3 * 2 ^ (p - h) := by
  set G := 2 ^ (p - h)
  have hG : 1 ≤ G := Nat.one_le_two_pow
  have hkG : 2 ^ k ≤ G := Nat.pow_le_pow_right two_pos hk
  have hlG : 2 ^ l ≤ G := Nat.pow_le_pow_right two_pos hl
  have hbank : (2 ^ k + 1) ^ K ≤ G :=
    calc (2 ^ k + 1) ^ K ≤ (2 ^ (k + 1)) ^ K := Nat.pow_le_pow_left (two_pow_add_one_le k) K
      _ ≤ G := by rw [← pow_mul]; exact Nat.pow_le_pow_right two_pos hK
  have hres : 2 ^ (2 * p) / 2 ^ (a * t) ≤ G := two_pow_div_le hh hat
  have htable : sparseTableBound k l K (2 ^ p) ≤ 2 ^ p / K + (9 * p + 8) * G := by
    have h₁ : (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) ≤ (2 * G) * (4 * p + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h₂ : (2 ^ k + 1) ^ K * (K + 1) ≤ G * (p + 1) := Nat.mul_le_mul hbank (by omega)
    unfold sparseTableBound
    nlinarith only [h₁, h₂, hlG, hG]
  have hhash : (k + l) * (4 * (2 * p) + 1) ≤ (16 * p ^ 2 + 2 * p) * G := by
    have := Nat.mul_le_mul hkl (le_refl (4 * (2 * p) + 1))
    nlinarith only [this, hG]
  have hfilter : (k + l) * (4 * (2 * p) + 1) + sparseTableBound k l K (2 ^ p) + 1 ≤
      2 ^ p / K + (16 * p ^ 2 + 11 * p + 9) * G := by nlinarith only [hhash, htable, hG]
  have hfilters := Nat.mul_le_mul_left t hfilter
  rw [mul_add] at hfilters
  have ht' : t * ((16 * p ^ 2 + 11 * p + 9) * G) ≤ (p + 1) * ((16 * p ^ 2 + 11 * p + 9) * G) :=
    Nat.mul_le_mul_right _ ht
  have hcube : (p + 1) * (16 * p ^ 2 + 11 * p + 9) + (4 * p + 6) ≤ 32 * (p + 1) ^ 3 := by
    nlinarith only []
  have hres' := Nat.mul_le_mul_right (2 * (2 * p) + 2) hres
  have hcubeG := Nat.mul_le_mul_right G hcube
  unfold indicatorBound
  linarith

/-- The partial function construction on `2 p` inputs costs at most its leading term
`⌊2 ^ p / J⌋` plus `32 (p + 1) ^ 3 2 ^ (p - h)`, when the tables and the collisions fit in `p - h`
bits. -/
private theorem partialBound_le {p h k l J w : ℕ} (hh : h ≤ p) (hk : k ≤ p - h)
    (hl : l ≤ p - h) (hkl : k + l ≤ 2 * p) (hkl' : p + h ≤ k + l) (hJ : 4 * k + 5 + J ≤ p - h)
    (hw : w ≤ 2 ^ p) :
    partialBound (2 * p) k l J w ≤ 2 ^ p / J + 32 * (p + 1) ^ 3 * 2 ^ (p - h) := by
  set G := 2 ^ (p - h)
  have hG : 1 ≤ G := Nat.one_le_two_pow
  have hkG : 2 ^ k ≤ G := Nat.pow_le_pow_right two_pos hk
  have hlG : 2 ^ l ≤ G := Nat.pow_le_pow_right two_pos hl
  have hbank : (2 ^ k + 1) ^ 3 * (2 * 2 ^ k + 1) * 2 ^ J ≤ G :=
    calc (2 ^ k + 1) ^ 3 * (2 * 2 ^ k + 1) * 2 ^ J
        ≤ (2 ^ (k + 1)) ^ 3 * 2 ^ (k + 2) * 2 ^ J := by
          gcongr
          · exact two_pow_add_one_le k
          · rw [pow_add]; have := Nat.one_le_two_pow (n := k); omega
      _ = 2 ^ (4 * k + 5 + J) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
      _ ≤ G := Nat.pow_le_pow_right two_pos hJ
  have hwJ : w / J ≤ 2 ^ p / J := Nat.div_le_div_right hw
  have hcoll : w * w / 2 ^ (k + l) ≤ G :=
    (Nat.div_le_div_right (by rw [two_mul, pow_add]; exact Nat.mul_le_mul hw hw)).trans
      (two_pow_div_le hh hkl')
  have htable : partialTableBound k l J w ≤ 2 ^ p / J + (8 * p + 8) * G := by
    have h₁ : (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) ≤ (2 * G) * (4 * p + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold partialTableBound
    nlinarith only [h₁, hbank, hlG, hG, hwJ]
  have hhash : (k + l) * (4 * (2 * p) + 1) ≤ (16 * p ^ 2 + 2 * p) * G := by
    have := Nat.mul_le_mul hkl (le_refl (4 * (2 * p) + 1))
    nlinarith only [this, hG]
  have hcoll' := Nat.mul_le_mul_right (2 * (2 * p) + 2) hcoll
  have hcube : 16 * p ^ 2 + 14 * p + 15 ≤ 32 * (p + 1) ^ 3 := by nlinarith only []
  have hcubeG := Nat.mul_le_mul_right G hcube
  unfold partialBound
  nlinarith only [htable, hhash, hcoll', hcubeG, hG]

/-- `c (v / d) ≤ L v` when `c ≤ L d`. -/
private theorem mul_div_le_mul {c L d : ℕ} (v : ℕ) (h : c ≤ L * d) : c * (v / d) ≤ L * v :=
  calc c * (v / d) ≤ L * d * (v / d) := Nat.mul_le_mul_right _ h
    _ = L * (d * (v / d)) := by ring
    _ ≤ L * v := Nat.mul_le_mul_left _ (Nat.mul_div_le v d)

/-- The constraints on the parameters, for `q ≥ 32 (P + 1)`, `c = q ^ 2 - 4 q - 6`, `h ≥ 2 q`
and `q ^ 2 h ≤ p < q ^ 2 (h + 1)`. -/
private theorem parameters_spec {P q p h c : ℕ} (hq : 32 * (P + 1) ≤ q)
    (hcq : c + 4 * q + 6 = q ^ 2) (hh : 2 * q ≤ h) (hlo : q ^ 2 * h ≤ p)
    (hhi : p < q ^ 2 * (h + 1)) :
    h ≤ p ∧ q * h ≤ p ∧ (q + 1) * h ≤ p - h ∧ (q + 1) * h + (p - h) = p + q * h ∧
      ((q + 1) * h + 1) * (q - 2) ≤ p - h ∧ p + h ≤ q * h * (q + 1) ∧
      4 * ((q + 1) * h) + 5 + c * h ≤ p - h ∧ 0 < q - 2 ∧ 0 < c * h ∧
      2 * P * (q + 1) ≤ (2 * P + 1) * (q - 2) ∧ 2 * P * p ≤ (2 * P + 1) * (c * h) := by
  have hq2 : q * 32 ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left q (by omega)
  have hh1 : 1 ≤ h := by omega
  have hqh : q * h ≤ p := le_trans (Nat.mul_le_mul_right h (by omega)) hlo
  have hhp : h ≤ p := le_trans (Nat.le_mul_of_pos_left h (by omega)) hqh
  have hq2h : q * 32 * h ≤ q ^ 2 * h := Nat.mul_le_mul_right h hq2
  have hk : (q + 1) * h ≤ p - h := by
    have : (q + 1) * h + h = q * h + 2 * h := by ring
    have : q * h + 2 * h ≤ q * 32 * h := by
      calc q * h + 2 * h = (q + 2) * h := by ring
        _ ≤ q * 32 * h := Nat.mul_le_mul_right h (by omega)
    omega
  have hkl : (q + 1) * h + (p - h) = p + q * h := by
    have : (q + 1) * h = q * h + h := by ring
    omega
  have hK : ((q + 1) * h + 1) * (q - 2) ≤ p - h := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    have key : ((r + 2 + 1) * h + 1) * r + h ≤ (r + 2) ^ 2 * h := by
      nlinarith only [Nat.le_mul_of_pos_right r hh1]
    omega
  have hat : p + h ≤ q * h * (q + 1) := by
    have e₁ : q * h * (q + 1) = q ^ 2 * h + q * h := by ring
    have e₂ : q ^ 2 * (h + 1) = q ^ 2 * h + q ^ 2 := by ring
    have h₁ : q ^ 2 + h ≤ q * h := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      have : r * (2 * (r + 1)) ≤ r * h := Nat.mul_le_mul_left r hh
      nlinarith only [this, hq]
    omega
  have hJ : 4 * ((q + 1) * h) + 5 + c * h ≤ p - h := by
    have e₁ : (c + 4 * q + 6) * h = q ^ 2 * h := by rw [hcq]
    have e₂ : (c + 4 * q + 6) * h = c * h + 4 * (q * h) + 6 * h := by ring
    have e₃ : 4 * ((q + 1) * h) = 4 * (q * h) + 4 * h := by ring
    omega
  have hcpos : 0 < c := by nlinarith only [hcq, hq]
  refine ⟨hhp, hqh, hk, hkl, hK, hat, hJ, by omega, Nat.mul_pos hcpos hh1, ?_, ?_⟩
  · obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    nlinarith only [hq]
  · have h₁ : 2 * P * p ≤ 2 * P * (q ^ 2 * (h + 1)) := Nat.mul_le_mul_left _ hhi.le
    have h₂ : 2 * P * q ^ 2 ≤ P * q * h := by
      have := Nat.mul_le_mul_left (P * q) hh
      nlinarith only [this]
    have h₃ : (2 * P + 1) * (4 * q + 6) ≤ 11 * (P + 1) * q := by nlinarith only [hq]
    have e₁ : (2 * P + 1) * (c * h) + (2 * P + 1) * (4 * q + 6) * h =
        (2 * P + 1) * q ^ 2 * h := by
      rw [← hcq]
      ring
    have h₄ : 12 * (P + 1) * q * h ≤ q ^ 2 * h :=
      Nat.mul_le_mul_right h (by nlinarith only [hq])
    nlinarith only [h₁, h₂, h₃, e₁, h₄, hh]

/-- **The parameters.** Let `q ≥ 32 (P + 1)`, `h ≥ 2 q` and `q ^ 2 h ≤ p < q ^ 2 (h + 1)`. Take
`k = (q + 1) h` column bits and `l = p - h` row bits, chunks of `K = q - 2` columns in sparse
tables and of `J = (q ^ 2 - 4 q - 6) h` entries in partial tables, and `t = q + 1` filters with
hashes to `k + l = p + q h` bits. Then the sparse indicator construction costs at most
`(1 + 1 / (2 P)) 2 ^ p` gates and the partial function construction at most
`(1 + 1 / (2 P)) 2 ^ p / p`, up to an error of `32 (p + 1) ^ 3 2 ^ (p - h)`. -/
private theorem two_mul_complexity_le {P q p h c : ℕ} (hq : 32 * (P + 1) ≤ q)
    (hcq : c + 4 * q + 6 = q ^ 2) (hh : 2 * q ≤ h) (hlo : q ^ 2 * h ≤ p)
    (hhi : p < q ^ 2 * (h + 1)) (D : Finset (BitString (2 * p))) (hD : #D ≤ 2 ^ p) :
    2 * P * complexity interpretation (single fun x => decide (x ∈ D)) ≤
        (2 * P + 1) * 2 ^ p + 2 * P * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) ∧
      ∀ u : BooleanFunction (2 * p), 2 * P * p * complexityOn interpretation D (single u) ≤
        (2 * P + 1) * 2 ^ p + 2 * P * p * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) := by
  obtain ⟨hhp, hqh, hk, hkl, hK, hat, hJ, hKpos, hJpos, hmainK, hmainJ⟩ :=
    parameters_spec hq hcq hh hlo hhi
  refine ⟨?_, fun u => ?_⟩
  · have hle := (complexity_indicator_le_indicatorBound D hD hkl hKpos (q + 1)).trans
      (indicatorBound_le hhp hk le_rfl (by omega) hK (by omega) (by omega) hat)
    have hmain := mul_div_le_mul (2 ^ p) hmainK
    calc 2 * P * complexity interpretation (single fun x => decide (x ∈ D))
        ≤ 2 * P * ((q + 1) * (2 ^ p / (q - 2)) + 32 * (p + 1) ^ 3 * 2 ^ (p - h)) :=
          Nat.mul_le_mul_left _ hle
      _ = 2 * P * (q + 1) * (2 ^ p / (q - 2)) + 2 * P * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) := by
          ring
      _ ≤ (2 * P + 1) * 2 ^ p + 2 * P * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) :=
          Nat.add_le_add_right hmain _
  · have hhq : h ≤ q * h := Nat.le_mul_of_pos_left h (by omega)
    have hle := (complexityOn_le_partialBound ((q + 1) * h) (p - h) D u hJpos).trans
      (partialBound_le hhp hk le_rfl (by omega) (by omega) hJ hD)
    have hmain := mul_div_le_mul (2 ^ p) hmainJ
    calc 2 * P * p * complexityOn interpretation D (single u)
        ≤ 2 * P * p * (2 ^ p / (c * h) + 32 * (p + 1) ^ 3 * 2 ^ (p - h)) :=
          Nat.mul_le_mul_left _ hle
      _ = 2 * P * p * (2 ^ p / (c * h)) + 2 * P * p * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) := by
          ring
      _ ≤ (2 * P + 1) * 2 ^ p + 2 * P * p * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) :=
          Nat.add_le_add_right hmain _

/-- **Uniform sparse and partial synthesis, in natural numbers.** For every `P`, for all large
`p`, the indicator of a set of at most `2 ^ p` of the `2 ^ (2 p)` inputs costs at most
`(1 + 1 / P) 2 ^ p` gates, and a function on such a set at most `(1 + 1 / P) 2 ^ p / p`. The
error terms are absorbed by taking `h = ⌊p / q ^ 2⌋`, which grows linearly with `p`. -/
private theorem eventually_complexity_le (P : ℕ) :
    ∀ᶠ p in atTop, ∀ D : Finset (BitString (2 * p)), #D ≤ 2 ^ p →
      P * complexity interpretation (single fun x => decide (x ∈ D)) ≤ (P + 1) * 2 ^ p ∧
      ∀ u : BooleanFunction (2 * p),
        P * p * complexityOn interpretation D (single u) ≤ (P + 1) * 2 ^ p := by
  obtain ⟨q, hq⟩ : ∃ q, q = 32 * (P + 1) := ⟨_, rfl⟩
  have hq6 : 4 * q + 6 ≤ q ^ 2 := by
    have : 32 ≤ q := by omega
    nlinarith only [this]
  obtain ⟨c, hc⟩ : ∃ c, c + 4 * q + 6 = q ^ 2 := ⟨q ^ 2 - (4 * q + 6), by omega⟩
  obtain ⟨H, hH⟩ := eventually_atTop.mp
    (Nat.eventually_mul_pow_le_pow (3456 * P * q ^ 8) 4 Nat.one_lt_two)
  filter_upwards [eventually_ge_atTop (q ^ 2 * (H + 2 * q + 1))] with p hp D hD
  have hq2 : 0 < q ^ 2 := by subst hq; positivity
  obtain ⟨h, hh⟩ : ∃ h, h = p / q ^ 2 := ⟨_, rfl⟩
  have hlo : q ^ 2 * h ≤ p := hh ▸ Nat.mul_div_le p (q ^ 2)
  have hhi : p < q ^ 2 * (h + 1) := hh ▸ Nat.lt_mul_div_succ p hq2
  have hhH : H + 2 * q + 1 ≤ h :=
    hh ▸ (Nat.le_div_iff_mul_le hq2).mpr (by rw [mul_comm]; exact hp)
  obtain ⟨hind, hpart⟩ := two_mul_complexity_le (P := P) hq.ge hc (by omega) hlo hhi D hD
  have hhp : h ≤ p := le_trans (Nat.le_mul_of_pos_left h hq2) hlo
  have hp1 : 1 ≤ p := by omega
  have herr : 2 * P * p * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) ≤ 2 ^ p := by
    have hpq : p ≤ 2 * q ^ 2 * h := by nlinarith only [hhi, (by omega : 1 ≤ h)]
    have hpq' : p + 1 ≤ 3 * q ^ 2 * h := by nlinarith only [hhi, (by omega : 1 ≤ h)]
    have hpoly : 2 * P * p * (32 * (p + 1) ^ 3) ≤ 3456 * P * q ^ 8 * h ^ 4 :=
      calc 2 * P * p * (32 * (p + 1) ^ 3)
          ≤ 2 * P * (2 * q ^ 2 * h) * (32 * (3 * q ^ 2 * h) ^ 3) := by gcongr
        _ = 3456 * P * q ^ 8 * h ^ 4 := by ring
    calc 2 * P * p * (32 * (p + 1) ^ 3 * 2 ^ (p - h))
        = 2 * P * p * (32 * (p + 1) ^ 3) * 2 ^ (p - h) := by ring
      _ ≤ 2 ^ h * 2 ^ (p - h) := Nat.mul_le_mul_right _ (hpoly.trans (hH h (by omega)))
      _ = 2 ^ p := by rw [← pow_add, Nat.add_sub_cancel' hhp]
  refine ⟨Nat.le_of_mul_le_mul_left ?_ two_pos, fun u => Nat.le_of_mul_le_mul_left ?_ two_pos⟩
  · have : 2 * P * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) ≤
        2 * P * p * (32 * (p + 1) ^ 3 * 2 ^ (p - h)) :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hp1)
    calc 2 * (P * complexity interpretation (single fun x => decide (x ∈ D)))
        = 2 * P * complexity interpretation (single fun x => decide (x ∈ D)) := by ring
      _ ≤ (2 * P + 1) * 2 ^ p + 2 ^ p := hind.trans (by omega)
      _ = 2 * ((P + 1) * 2 ^ p) := by ring
  · calc 2 * (P * p * complexityOn interpretation D (single u))
        = 2 * P * p * complexityOn interpretation D (single u) := by ring
      _ ≤ (2 * P + 1) * 2 ^ p + 2 ^ p := (hpart u).trans (by omega)
      _ = 2 * ((P + 1) * 2 ^ p) := by ring

/-! ### Uniform sparse and partial synthesis -/

/-- **From natural-number bounds to `ε`.** For every `ε > 0` there is `P > 0` such that a bound
`P x ≤ (a P + b) y` in natural numbers gives `x ≤ (a + ε) y`: the error `b` is at most `ε P`. -/
private theorem exists_le_add_mul_of_mul_le (a b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, ∀ x y : ℕ, P * x ≤ (a * P + b) * y → (x : ℝ) ≤ (a + ε) * y := by
  obtain ⟨P, hP⟩ := exists_nat_gt (b / ε)
  have hP0 : (0 : ℝ) < P := lt_of_le_of_lt (by positivity) hP
  have hb : (b : ℝ) ≤ ε * P := by
    have := (div_lt_iff₀ hε).mp hP
    linarith
  refine ⟨P, fun x y h => (mul_le_mul_iff_right₀ hP0).mp ?_⟩
  have h' : (P : ℝ) * x ≤ (a * P + b) * y := by exact_mod_cast h
  nlinarith [mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ y)]

/-- **Sparse indicators.** For every `ε > 0` and all large `p`, the indicator of any set of at
most `2 ^ p` of the `2 ^ (2 p)` inputs has a De Morgan circuit with at most `(1 + ε) 2 ^ p`
gates. This is the case `N = 2 ^ p` of Lupanov's bound for functions with `N` ones, which is
asymptotically optimal [Lupanov1965], [Chashkin, Theorem 3.1][Chashkin2024]. -/
theorem complexity_indicator_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ D : Finset (BitString (2 * p)), #D ≤ 2 ^ p →
      (complexity interpretation (single fun x => decide (x ∈ D)) : ℝ) ≤ (1 + ε) * 2 ^ p := by
  obtain ⟨P, hP⟩ := exists_le_add_mul_of_mul_le 1 1 hε
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp (eventually_complexity_le P)
  refine ⟨p₀, fun p hp D hD => ?_⟩
  simpa using hP _ (2 ^ p) (by simpa using (hp₀ p hp D hD).1)

/-- **Partial functions.** For every `ε > 0` and all large `p`, every Boolean function on any
set of at most `2 ^ p` of the `2 ^ (2 p)` inputs agrees on that set with a De Morgan circuit
with at most `(1 + ε) 2 ^ p / p` gates. This is the case `D = 2 ^ p` of Sholomov's bound
`D / log₂ D` for functions defined on `D` inputs, which is asymptotically optimal
[Sholomov1969], [Chashkin, Theorem 2.1][Chashkin2024]. -/
theorem complexityOn_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ D : Finset (BitString (2 * p)), #D ≤ 2 ^ p →
      ∀ u : BooleanFunction (2 * p),
        (complexityOn interpretation D (single u) : ℝ) ≤ (1 + ε) * 2 ^ p / p := by
  obtain ⟨P, hP⟩ := exists_le_add_mul_of_mul_le 1 1 hε
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp (eventually_complexity_le P)
  refine ⟨max p₀ 1, fun p hp D hD u => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [le_div_iff₀ hp0, mul_comm]
  have := hP (p * complexityOn interpretation D (single u)) (2 ^ p) (by
    simpa [mul_assoc] using (hp₀ p (le_of_max_le_left hp) D hD).2 u)
  simpa using this

/-! ### Square-root continuity of circuit complexity -/

/-- **Square-root continuity, in natural numbers.** For every `P`, for all large `p`, changing a
function with any number of outputs on at most `2 ^ p` of its `2 ^ (2 p)` inputs, and in at most
`2 p` of its outputs, changes its complexity by at most `(3 + 4 / P) 2 ^ p`. -/
private theorem eventually_mul_dist_complexity_le (P : ℕ) :
    ∀ᶠ p in atTop, ∀ (m : ℕ) (f g : BitString (2 * p) → BitString m),
      hammingDist f g ≤ 2 ^ p → hammingDist (Function.swap f) (Function.swap g) ≤ 2 * p →
      P * Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
        (3 * P + 4) * 2 ^ p := by
  filter_upwards [eventually_complexity_le P,
    Nat.eventually_mul_pow_le_pow (10 * P) 1 Nat.one_lt_two, eventually_ge_atTop 1]
    with p hsynth hsmall hp m f g hrows hcols
  let D : Finset (BitString (2 * p)) := {x | f x ≠ g x}
  let O : Finset (Fin m) := {j | Function.swap f j ≠ Function.swap g j}
  have hD : #D ≤ 2 ^ p := hrows
  have hO : #O ≤ 2 * p := hcols
  let select : Fin #O → Fin m := O.orderEmbOfFin rfl
  have hselect : ∀ j ∉ Set.range select, ∀ x, f x j = g x j := by
    intro j hj x
    have hjO : j ∉ O := by
      rwa [show Set.range select = O from range_orderEmbOfFin O rfl] at hj
    have hfg : Function.swap f j = Function.swap g j := by simpa [O] using hjO
    exact congrFun hfg x
  have hdist := dist_complexity_le_sum_of_cover f g D select
    (fun x hx => by simpa [D] using hx) hselect
  obtain ⟨hind, hpart⟩ := hsynth D hD
  have hlabels : P * p * ∑ i, complexityOn interpretation D
      (single fun x => f x (select i) ^^ g x (select i)) ≤ #O * ((P + 1) * 2 ^ p) := by
    rw [mul_sum]
    calc ∑ i, P * p * complexityOn interpretation D
          (single fun x => f x (select i) ^^ g x (select i))
        ≤ ∑ _i : Fin #O, (P + 1) * 2 ^ p := sum_le_sum fun i _ => hpart _
      _ = #O * ((P + 1) * 2 ^ p) := by simp
  have hlabels' : P * ∑ i, complexityOn interpretation D
      (single fun x => f x (select i) ^^ g x (select i)) ≤ 2 * ((P + 1) * 2 ^ p) := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < p by omega)
    calc p * (P * ∑ i, complexityOn interpretation D
          (single fun x => f x (select i) ^^ g x (select i)))
        = P * p * ∑ i, complexityOn interpretation D
          (single fun x => f x (select i) ^^ g x (select i)) := by ring
      _ ≤ #O * ((P + 1) * 2 ^ p) := hlabels
      _ ≤ 2 * p * ((P + 1) * 2 ^ p) := Nat.mul_le_mul_right _ hO
      _ = p * (2 * ((P + 1) * 2 ^ p)) := by ring
  have hgates : P * (5 * #O) ≤ 2 ^ p := by
    have := Nat.mul_le_mul_left (5 * P) hO
    simp only [pow_one] at hsmall
    nlinarith only [this, hsmall]
  calc P * Nat.dist (complexity interpretation f) (complexity interpretation g)
      ≤ P * (complexity interpretation (single fun x => decide (x ∈ D)) +
          ∑ i, complexityOn interpretation D
            (single fun x => f x (select i) ^^ g x (select i)) + 5 * #O) :=
        Nat.mul_le_mul_left P hdist
    _ = P * complexity interpretation (single fun x => decide (x ∈ D)) +
          P * ∑ i, complexityOn interpretation D
            (single fun x => f x (select i) ^^ g x (select i)) + P * (5 * #O) := by ring
    _ ≤ (P + 1) * 2 ^ p + 2 * ((P + 1) * 2 ^ p) + 2 ^ p :=
        Nat.add_le_add (Nat.add_le_add hind hlabels') hgates
    _ = (3 * P + 4) * 2 ^ p := by ring

/-- **Square-root continuity of circuit complexity.** For every `ε > 0` and all large `p`,
changing a Boolean function with any number of outputs on at most `2 ^ p` of its `2 ^ (2 p)`
inputs, and in at most `2 p` of its outputs, changes its De Morgan circuit complexity by at most
`(3 + ε) 2 ^ p`, where `2 ^ p` is the square root of the number of inputs. The changes are
corrected by `dist_complexity_le_sum_of_cover`, with the indicator of the changed inputs computed
by `complexity_indicator_le` and each changed output by `complexityOn_le`. The order `2 ^ p` is
optimal by `exists_hammingDist_eq_le_dist_complexity`. -/
theorem dist_complexity_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ (m : ℕ) (f g : BitString (2 * p) → BitString m),
      hammingDist f g ≤ 2 ^ p → hammingDist (Function.swap f) (Function.swap g) ≤ 2 * p →
      (Nat.dist (complexity interpretation f) (complexity interpretation g) : ℝ) ≤
        (3 + ε) * 2 ^ p := by
  obtain ⟨P, hP⟩ := exists_le_add_mul_of_mul_le 3 4 hε
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp (eventually_mul_dist_complexity_le P)
  refine ⟨p₀, fun p hp m f g hrows hcols => ?_⟩
  simpa using hP _ (2 ^ p) (hp₀ p hp m f g hrows hcols)

/-- **Square-root continuity for a single output.** For every `ε > 0` and all large `p`, changing
a Boolean function on at most `2 ^ p` of its `2 ^ (2 p)` inputs changes its De Morgan circuit
complexity by at most `(1 + ε) 2 ^ p`. -/
theorem dist_complexity_single_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ f g : BooleanFunction (2 * p), hammingDist f g ≤ 2 ^ p →
      (Nat.dist (complexity interpretation (single f)) (complexity interpretation (single g)) :
        ℝ) ≤ (1 + ε) * 2 ^ p := by
  obtain ⟨P, hP⟩ := exists_le_add_mul_of_mul_le 1 2 hε
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp ((eventually_complexity_le P).and
    (Nat.eventually_mul_pow_le_pow (4 * P) 0 Nat.one_lt_two))
  refine ⟨p₀, fun p hp f g hfg => ?_⟩
  obtain ⟨hsynth, hsmall⟩ := hp₀ p hp
  let D : Finset (BitString (2 * p)) := {x | f x ≠ g x}
  have hxor : (fun x => f x ^^ g x) = fun x => decide (x ∈ D) := by
    funext x
    by_cases h : f x = g x <;> simp [D, h]
  have hdist := dist_complexity_single_le_complexity_xor f g
  rw [hxor] at hdist
  have hind := (hsynth D hfg).1
  simp only [pow_zero, mul_one] at hsmall
  have hnat : P * Nat.dist (complexity interpretation (single f))
      (complexity interpretation (single g)) ≤ (1 * P + 2) * 2 ^ p := by
    have := Nat.mul_le_mul_left P hdist
    nlinarith only [this, hind, hsmall]
  simpa using hP _ (2 ^ p) hnat

/-- **Exact hardness survives sparse errors.** For every `ε > 0` and all large `p`, if a
function `f` with at most `2 p` outputs on `2 p` inputs has complexity more than
`(3 + ε) 2 ^ p` above that of `g`, then `f` and `g` differ on more than `2 ^ p` inputs. -/
theorem lt_hammingDist_of_complexity_add_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ m ≤ 2 * p, ∀ f g : BitString (2 * p) → BitString m,
      (complexity interpretation g : ℝ) + (3 + ε) * 2 ^ p < complexity interpretation f →
        2 ^ p < hammingDist f g := by
  obtain ⟨p₀, hp₀⟩ := dist_complexity_le ε hε
  refine ⟨p₀, fun p hp m hm f g hfg => not_le.mp fun hrows => ?_⟩
  have hcols : hammingDist (Function.swap f) (Function.swap g) ≤ 2 * p :=
    (hammingDist_le_card_fintype).trans (by simpa using hm)
  have hdist := hp₀ p hp m f g hrows hcols
  have htri : (complexity interpretation f : ℝ) ≤ complexity interpretation g +
      Nat.dist (complexity interpretation f) (complexity interpretation g) := by
    exact_mod_cast Nat.dist_tri_right' _ _
  linarith

/-- **Sparse changes are negligible for hard functions.** If `f p` and `g p` have `2 p` inputs,
and eventually differ on at most `2 ^ p` inputs and in at most `2 p` outputs, and
`2 ^ p = o(C(f p))`, then `|C(f p) - C(g p)| = o(C(f p))`. -/
theorem dist_complexity_isLittleO {m : ℕ → ℕ}
    (f g : (p : ℕ) → BitString (2 * p) → BitString (m p))
    (hrows : ∀ᶠ p in atTop, hammingDist (f p) (g p) ≤ 2 ^ p)
    (hcols : ∀ᶠ p in atTop, hammingDist (Function.swap (f p)) (Function.swap (g p)) ≤ 2 * p)
    (hf : (fun p => (2 : ℝ) ^ p) =o[atTop] fun p => (complexity interpretation (f p) : ℝ)) :
    (fun p => (Nat.dist (complexity interpretation (f p)) (complexity interpretation (g p)) :
      ℝ)) =o[atTop] fun p => (complexity interpretation (f p) : ℝ) := by
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hf
  obtain ⟨p₀, hp₀⟩ := dist_complexity_le 1 one_pos
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop p₀, hrows, hcols] with p hp hr hc
  have := hp₀ p hp (m p) (f p) (g p) hr hc
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  linarith

/-! ### Optimality -/

/-- The graph of a map from `p` bits to `p` bits: a set of `2 ^ p` inputs on `p + p` bits. -/
private def graphFinset {p : ℕ} (φ : BitString p → BitString p) : Finset (BitString (p + p)) :=
  univ.image fun x => Fin.append x (φ x)

/-- A point of a graph determines its argument and its value. -/
private theorem eq_and_eq_of_append_eq {p : ℕ} {x y u v : BitString p}
    (h : (Fin.append x u : BitString (p + p)) = Fin.append y v) : x = y ∧ u = v :=
  ⟨funext fun i => by simpa only [Fin.append_left] using congrFun h (Fin.castAdd p i),
    funext fun i => by simpa only [Fin.append_right] using congrFun h (Fin.natAdd p i)⟩

private theorem card_graphFinset {p : ℕ} (φ : BitString p → BitString p) :
    #(graphFinset φ) = 2 ^ p := by
  rw [graphFinset, card_image_of_injective _ fun x y h => (eq_and_eq_of_append_eq h).1]
  simp

/-- Distinct maps have distinct graphs. -/
private theorem graphFinset_injective (p : ℕ) :
    Function.Injective (graphFinset (p := p)) := fun φ ψ h => by
  funext x
  obtain ⟨y, -, hy⟩ := mem_image.mp (h ▸ mem_image_of_mem _ (mem_univ x) :
    Fin.append x (φ x) ∈ graphFinset ψ)
  obtain ⟨rfl, hψ⟩ := eq_and_eq_of_append_eq hy
  exact hψ.symm

/-- Fewer functions on `p + p` bits have circuits with `2 ^ (p - 4)` gates than there are maps
from `p` bits to `p` bits. The count of circuits does not even need its factorial saving. -/
private theorem card_computableFunctions_lt {p : ℕ} (hp : 4 ≤ p) :
    #(computableFunctions (p + p) (2 ^ (p - 4))) < 2 ^ (p * 2 ^ p) := by
  set s := 2 ^ (p - 4)
  have hs : 2 ^ p = 16 * s := by
    rw [show p = 4 + (p - 4) by omega, pow_add]
    simp [s]
  have hs1 : 1 ≤ s := Nat.one_le_two_pow
  have hpp : p + p ≤ 2 ^ p := by
    have : ∀ q, 1 ≤ q → 2 * q ≤ 2 ^ q := fun q hq => by
      induction q, hq using Nat.le_induction with
      | base => decide
      | succ q _ ih => rw [pow_succ]; omega
    simpa [two_mul] using this p (by omega)
  have hwires : p + p + s + 1 ≤ 2 ^ (p + 1) := by rw [pow_succ]; omega
  have hlines : 5 * (p + p + s + 1) ^ 2 ≤ 2 ^ (2 * p + 5) :=
    calc 5 * (p + p + s + 1) ^ 2 ≤ 8 * (2 ^ (p + 1)) ^ 2 := by gcongr; omega
      _ = 2 ^ (2 * p + 5) := by rw [← pow_mul, show (8 : ℕ) = 2 ^ 3 by rfl, ← pow_add]; ring_nf
  have hcount := (Nat.le_mul_of_pos_right _ (Nat.factorial_pos s)).trans
    (card_computableFunctions_mul_factorial_le (p + p) s)
  have hexp : p + (2 * p + 5) * s + (p + 1) < p * 2 ^ p := by
    rw [hs]
    nlinarith only [hp, hs1]
  calc #(computableFunctions (p + p) s)
      ≤ (s + 1) * (5 * (p + p + s + 1) ^ 2) ^ s * (p + p + s) := hcount
    _ ≤ 2 ^ p * (2 ^ (2 * p + 5)) ^ s * 2 ^ (p + 1) := by
      gcongr
      · omega
      · rw [pow_succ]; omega
    _ = 2 ^ (p + (2 * p + 5) * s + (p + 1)) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ < 2 ^ (p * 2 ^ p) := Nat.pow_lt_pow_right one_lt_two hexp

/-- Some graph of a map from `p` bits to `p` bits has a hard indicator. -/
private theorem exists_hard_graphFinset {p : ℕ} (hp : 4 ≤ p) :
    ∃ D : Finset (BitString (p + p)), #D = 2 ^ p ∧
      2 ^ (p - 4) < complexity interpretation (single fun x => decide (x ∈ D)) := by
  let family : Finset (BooleanFunction (p + p)) :=
    univ.image fun φ : BitString p → BitString p => fun x => decide (x ∈ graphFinset φ)
  have hinj : Function.Injective
      fun φ : BitString p → BitString p => fun x => decide (x ∈ graphFinset φ) :=
    fun φ ψ h => graphFinset_injective p (Finset.ext fun x => by
      simpa using congrFun h x)
  have hcard : #family = 2 ^ (p * 2 ^ p) := by
    rw [card_image_of_injective _ hinj]
    simp [← pow_mul]
  obtain ⟨f, hf, hhard⟩ := exists_mem_notMem_of_card_lt_card
    ((card_computableFunctions_lt hp).trans_eq hcard.symm)
  obtain ⟨φ, -, rfl⟩ := mem_image.mp hf
  refine ⟨graphFinset φ, card_graphFinset φ, not_le.mp fun h => hhard ?_⟩
  exact mem_computableFunctions.mpr (complexity_le_iff.mp h)

/-- **Hard sparse indicators.** For `p ≥ 4`, the indicator of some set of exactly `2 ^ p` of
the `2 ^ (2 p)` inputs has complexity more than `2 ^ p / 16`. By counting, as in Shannon's lower
bound: there are more sets of this size than functions with small circuits. -/
theorem exists_hard_indicator {p : ℕ} (hp : 4 ≤ p) :
    ∃ D : Finset (BitString (2 * p)), #D = 2 ^ p ∧
      2 ^ (p - 4) < complexity interpretation (single fun x => decide (x ∈ D)) := by
  rw [two_mul]
  exact exists_hard_graphFinset hp

/-- **Square-root continuity is optimal.** For `p ≥ 4`, some function on `2 p` inputs differs
from the constant `false` on exactly `2 ^ p` inputs, and its complexity differs from that of
the constant by at least `2 ^ p / 16`. -/
theorem exists_hammingDist_eq_le_dist_complexity {p : ℕ} (hp : 4 ≤ p) :
    ∃ f : BooleanFunction (2 * p), hammingDist f (fun _ => false) = 2 ^ p ∧
      2 ^ p ≤ 16 * Nat.dist (complexity interpretation (single f))
        (complexity interpretation (single fun _ : BitString (2 * p) => false)) := by
  obtain ⟨D, hD, hhard⟩ := exists_hard_indicator hp
  refine ⟨fun x => decide (x ∈ D), ?_, ?_⟩
  · rw [← hD]
    unfold hammingDist
    congr 1
    ext x
    simp
  · have hfalse : complexity interpretation (single fun _ : BitString (2 * p) => false) ≤ 1 :=
      (Synthesis.const false).complexity_le
    have hs : 2 ^ p = 16 * 2 ^ (p - 4) := by
      rw [show p = 4 + (p - 4) by omega, pow_add]
      norm_num
    rw [hs]
    generalize complexity interpretation (single fun x => decide (x ∈ D)) = a at hhard ⊢
    generalize complexity interpretation (single fun _ : BitString (2 * p) => false) = b
      at hfalse ⊢
    generalize 2 ^ (p - 4) = c at hhard ⊢
    unfold Nat.dist
    omega

/-- **No sparse continuity bound is `o(2 ^ p)`.** If `b p` eventually bounds the change in
complexity of every function on `2 p` inputs changed on at most `2 ^ p` inputs, then `b` is not
`o(2 ^ p)`. -/
theorem not_isLittleO_of_dist_complexity_le (b : ℕ → ℝ)
    (hb : ∀ᶠ p in atTop, ∀ f g : BooleanFunction (2 * p), hammingDist f g ≤ 2 ^ p →
      (Nat.dist (complexity interpretation (single f)) (complexity interpretation (single g)) :
        ℝ) ≤ b p) :
    ¬b =o[atTop] fun p => (2 : ℝ) ^ p := fun hsmall => by
  obtain ⟨p, hbp, hsmallp, hp⟩ :=
    (hb.and ((hsmall.def (show (0 : ℝ) < 1 / 32 by norm_num)).and (eventually_ge_atTop 4))).exists
  obtain ⟨f, hf, hlarge⟩ := exists_hammingDist_eq_le_dist_complexity hp
  have hcost := hbp f _ hf.le
  have hlarge' : (2 : ℝ) ^ p ≤ 16 * (Nat.dist (complexity interpretation (single f))
      (complexity interpretation (single fun _ : BitString (2 * p) => false)) : ℝ) := by
    exact_mod_cast hlarge
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ p)] at hsmallp
  have hpos : (0 : ℝ) < 2 ^ p := by positivity
  nlinarith [le_abs_self (b p), Real.norm_eq_abs (b p)]

/-! ### Shattering -/

/-- The sets of inputs on `n` bits whose indicators have De Morgan circuits with at most `s`
gates, the supports of `computableFunctions n s`: the concept class of circuits of size `s`. -/
noncomputable def circuitSets (n s : ℕ) : Finset (Finset (BitString n)) :=
  (computableFunctions n s).image fun f => ({x | f x = true} : Finset (BitString n))

/-- A set is in the concept class of circuits of size `s` exactly when a circuit with at most `s`
gates computes its indicator. -/
@[simp] theorem mem_circuitSets {n s : ℕ} {T : Finset (BitString n)} :
    T ∈ circuitSets n s ↔ ∃ c : Circuit signature n 1,
      c.Computes interpretation (single fun x => decide (x ∈ T)) ∧ c.size ≤ s := by
  simp only [circuitSets, mem_image, mem_computableFunctions]
  constructor
  · rintro ⟨f, ⟨c, hc, hs⟩, rfl⟩
    exact ⟨c, fun x => (hc x).trans (by simp), hs⟩
  · rintro ⟨c, hc, hs⟩
    exact ⟨_, ⟨c, hc, hs⟩, by ext x; simp⟩

/-- **Circuits shatter square-root-sized samples.** For every `ε > 0` and all large `p`, the
sets with circuits of `(1 + ε) 2 ^ p / p` gates shatter every set of at most `2 ^ p` of the
`2 ^ (2 p)` inputs: every subset of the sample is cut out by such a circuit. -/
theorem shatters_circuitSets (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ D : Finset (BitString (2 * p)), #D ≤ 2 ^ p →
      (circuitSets (2 * p) ⌊(1 + ε) * 2 ^ p / p⌋₊).Shatters D := by
  obtain ⟨p₀, hp₀⟩ := complexityOn_le ε hε
  refine ⟨p₀, fun p hp D hD t ht => ?_⟩
  obtain ⟨c, hc, hsize⟩ := exists_computesOn_size_eq_complexityOn (I := interpretation)
    (S := (D : Set (BitString (2 * p)))) (f := single fun x => decide (x ∈ t))
  let u : Finset (BitString (2 * p)) := {x | c.eval interpretation x 0 = true}
  refine ⟨u, mem_circuitSets.2 ⟨c, Circuit.computes_single_iff.2 fun x => by simp [u],
    Nat.le_floor (hsize ▸ hp₀ p hp D hD _)⟩, ?_⟩
  · ext x
    simp only [mem_inter, u, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hx, hcx⟩
      simpa [hc (mem_coe.mpr hx)] using hcx
    · intro hx
      refine ⟨ht hx, ?_⟩
      simpa [hc (mem_coe.mpr (ht hx))] using hx

/-- **The VC dimension of small circuits.** For every `ε > 0` and all large `p`, circuits with
`(1 + ε) 2 ^ p / p` gates on `2 p` inputs have VC dimension at least `2 ^ p`. -/
theorem le_vcDim_circuitSets (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, 2 ^ p ≤ (circuitSets (2 * p) ⌊(1 + ε) * 2 ^ p / p⌋₊).vcDim := by
  obtain ⟨p₀, hp₀⟩ := shatters_circuitSets ε hε
  refine ⟨p₀, fun p hp => ?_⟩
  obtain ⟨D, -, hD⟩ := exists_subset_card_eq (s := (univ : Finset (BitString (2 * p))))
    (by simpa using Nat.pow_le_pow_right two_pos (by omega : p ≤ 2 * p))
  simpa [hD] using (hp₀ p hp D hD.le).card_le_vcDim

end Cslib.Circuits.Boolean.SparseSynthesis
