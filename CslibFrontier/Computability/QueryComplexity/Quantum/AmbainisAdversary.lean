/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Progress
public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Foundations.Data.BitString.Flip
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Foundations.Quantum.Measurement.Overlap

/-!
# Ambainis's quantum adversary method

Let a `T`-query algorithm (`Cslib.Quantum.run`) with a unit initial state be run on related pairs
`(x, y) ∈ R` of inputs, and suppose that at the end the states on every related pair have overlap
`|⟨ψ_x, ψ_y⟩| ≤ δ`. Suppose also that every first input of `R` is related to at least `m` inputs
and every second input to at least `m'`, and that `l_{x,i} l_{y,i} ≤ L` for every related pair
`(x, y)` and every coordinate `i` with `x_i ≠ y_i`. Here `l_{x,i}` is the number of pairs of `R`
with first input `x` that differ at `i`, and `l_{y,i}` is the number with second input `y`. Then
`(1 - δ) √(m m') ≤ 2T √L` (`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt`), which is
[Ambainis2002], Theorem 6, for bit queries. If a measurement accepts every first input with
probability at least `1 - ε` and every second input with probability at most `ε ≤ 1/2`, then
`δ = 2√(ε(1-ε))` (`Cslib.Quantum.norm_inner_le_two_mul_sqrt_of_measureProb`, [Ambainis2002],
Lemma 1). Bounding `l_{x,i} ≤ l` and `l_{y,i} ≤ l'` gives [Ambainis2002], Theorem 2:
`(1 - 2√(ε(1-ε))) √(m m') ≤ 2T √(l l')`
(`Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt`).

Only the inputs that occur in `R` are constrained, so the bounds apply to promise problems and
partial functions: correctness is required only on those inputs. When the related pairs are the
neighbors `(x, x ⊕ eᵢ)` with `x ∈ A` and `x ⊕ eᵢ ∈ B`, `l = l' = 1`, and the bound reads
`(1 - δ) √(m m') ≤ 2T` with `m` and `m'` lower bounds on the numbers of neighbors across
(`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_neighbors`). The applications to parity,
threshold functions and majority are in the module
`CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.Symmetric`, and those to
Tribes and to the `AND` of `OR`s in
`CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.Tribes`.

**The argument.** Let `ψ_x^t` be the state after `t` queries on input `x`. The weighted
progress measure (`Cslib.Quantum.weightedProgress` in
`CslibFrontier.Computability.QueryComplexity.Quantum.Progress`) with unit weights sums
`S_t = ∑_{(x, y) ∈ R} |⟨ψ_x^t, ψ_y^t⟩|`.
* Before any query all states are equal, so `S_0 = |R|`. At the end `S_T ≤ δ |R|`.
* The oracles of `x` and `y` differ only on the query indices `i` with `x_i ≠ y_i`, so one query
  lowers `|⟨ψ_x, ψ_y⟩|` by at most `2 ∑_{i : x_i ≠ y_i} ‖Π_i ψ_x‖ ‖Π_i ψ_y‖`
  (`Cslib.Quantum.norm_inner_phaseOracle_phaseOracle_ge`), where `Π_i` is `Cslib.Quantum.ctrlProj`.
* For every `c > 0`, taking step weights `c √L / l_{x,i}` and `√L / (c l_{y,i})` in
  `Cslib.Quantum.one_sub_mul_sum_le_of_sq_le` bounds each step's loss by
  `√L (c |X| + |Y| / c)`, where `X` and `Y` are the sets of first and second inputs. Taking
  `c = √(|Y| / |X|)` gives `2 √L √(|X| |Y|)`.
* Finally `|R| ≥ m |X|` and `|R| ≥ m' |Y|`, so `|R| ≥ √(m m') √(|X| |Y|)`.

**Source mapping** (numbering of arXiv:quant-ph/0002066v1).
* `one_sub_mul_sqrt_le_two_mul_mul_sqrt` is Theorem 6 (§6.1) for `{0, 1}`-valued variables. The
  conclusion is stated through the final overlap `δ` on the related pairs rather than through a
  function `f`, so it holds for any output alphabet: Lemma 1 may be applied to each pair with the
  measurement of the answer `f(x)`.
* `norm_inner_le_two_mul_sqrt_of_measureProb` is Lemma 1 (§3), for one measurement.
* `one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt` is Theorem 2 (§5.1), for Boolean outputs
  read off one set `S` of measurement outcomes.
* `one_sub_mul_sqrt_le_two_mul_of_neighbors` is the case `l = l' = 1` of Theorem 2 that §5.3 uses
  for the `AND` of `OR`s (Theorem 4) and for majority and parity.

The source states `Ω(·)` bounds. The constants are those of this proof. As in the polynomial
method (`CslibFrontier.Computability.QueryComplexity.Quantum.Polynomial`), the bounds hold for each
algorithm. There is no separate definition of quantum query complexity.

## Main results

* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt`: `(1 - δ) √(m m') ≤ 2T √L`.
* `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt`:
  `(1 - 2√(ε(1-ε))) √(m m') ≤ 2T √(l l')`.
* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_neighbors` and
  `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_of_neighbors`: the bounds across single
  bit flips.

## References

* [A. Ambainis, *Quantum lower bounds by quantum arguments*][Ambainis2002]
-/

public section

namespace Cslib.Quantum

open Finset Function

variable {N : ℕ} {W : Type*} [Fintype W]

variable (U : ℕ → State N W →ₗᵢ[ℂ] State N W)

/-- **Ambainis's adversary bound** [Ambainis2002], Theorem 6, for bit queries: let `R` be a
nonempty set of pairs of inputs on which a `T`-query algorithm with a unit initial state ends in
states with overlap at most `δ`. If every first input of `R` lies in at least `m` pairs of `R` and
every second input in at least `m'`, and `l_{x,i} l_{y,i} ≤ L` for every `(x, y) ∈ R` and every
`i` with `x_i ≠ y_i`, where `l_{x,i}` counts the pairs of `R` with first input `x` that differ at
`i` and `l_{y,i}` those with second input `y`, then `(1 - δ) √(m m') ≤ 2T √L`. The constant is
that of this proof. The source states `Ω(√(m m' / l_max))`. -/
theorem one_sub_mul_sqrt_le_two_mul_mul_sqrt {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {R : Finset (BitString N × BitString N)} (hR : R.Nonempty) {δ : ℝ}
    (hδ : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ) {m m' L : ℕ}
    (hm : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1}) (hm' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2})
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L) :
    (1 - δ) * √(m * m') ≤ 2 * T * √L := by
  classical
  set X := R.image Prod.fst
  set Y := R.image Prod.snd
  have hX : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 (hR.image _)
  have hY : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 (hR.image _)
  -- `|R| ≥ m |X|` and `|R| ≥ m' |Y|`
  have hRX : (m : ℝ) * #X ≤ #R := by
    have : m * #X ≤ #R := by
      rw [card_eq_sum_card_image Prod.fst R, mul_comm, ← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
      exact hm p hp
    exact_mod_cast this
  have hRY : (m' : ℝ) * #Y ≤ #R := by
    have : m' * #Y ≤ #R := by
      rw [card_eq_sum_card_image Prod.snd R, mul_comm, ← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun y hy => ?_
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hy
      exact hm' p hp
    exact_mod_cast this
  -- the weighted progress bound with `c = √|Y| / √|X|`
  set x : ℝ := (#X : ℝ) with hx
  set y : ℝ := (#Y : ℝ) with hy
  set c : ℝ := √y / √x
  have hc : 0 < c := div_pos (Real.sqrt_pos.2 hY) (Real.sqrt_pos.2 hX)
  have hfib (k : BitString N × BitString N → BitString N) (s : ℝ) (hs : 0 ≤ s)
      (z : BitString N) (i : Fin N) :
      ∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = z,
        s / #{q ∈ R | q.1 i ≠ q.2 i ∧ k q = k p} ≤ s := by
    let S := R.filter fun p => p.1 i ≠ p.2 i ∧ k p = z
    rw [sum_congr rfl (g := fun _ => s / (#S : ℝ)) fun p hp => by
      simp only [S, (mem_filter.1 hp).2.2], sum_const, nsmul_eq_mul]
    by_cases h0 : #S = 0
    · simpa [h0] using hs
    · exact (mul_div_cancel₀ _ (by exact_mod_cast h0)).le
  have htel := one_sub_mul_sum_le_of_sq_le U hψ₀ T R (fun _ => (1 : ℝ)) hδ
    (fun p i => c * √L / #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1})
    (fun p i => (√L / c) / #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2})
    (fun _ => c * √L) (fun _ => √L / c) (fun _ _ => zero_le_one)
    (fun _ _ _ _ => by positivity) (fun _ _ _ _ => by positivity)
    (fun p hp i hi => by
      have hl₁ : (0 : ℝ) < #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} :=
        Nat.cast_pos.2 (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hi, rfl⟩⟩)
      have hl₂ : (0 : ℝ) < #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} :=
        Nat.cast_pos.2 (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hi, rfl⟩⟩)
      have hll : (#{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} : ℝ) *
          #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ √L * √L := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg L)]
        exact_mod_cast hL p hp i hi
      rw [one_pow]
      field_simp [hl₁.ne', hl₂.ne', hc.ne']
      nlinarith [hc])
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun z _ i => hfib Prod.fst (c * √L) (by positivity) z i)
    (fun z _ i => hfib Prod.snd (√L / c) (by positivity) z i)
  simp only [sum_const, nsmul_eq_mul, mul_one] at htel
  have hbal : c * √L * x + (√L / c) * y = √L * (2 * (√x * √y)) := by
    have h1 : 0 < √x := Real.sqrt_pos.2 hX
    have h2 : 0 < √y := Real.sqrt_pos.2 hY
    have ex : x = √x * √x := (Real.mul_self_sqrt hX.le).symm
    have ey : y = √y * √y := (Real.mul_self_sqrt hY.le).symm
    calc
      c * √L * x + (√L / c) * y
          = (√y / √x) * √L * (√x * √x) + (√L / (√y / √x)) * (√y * √y) := by
            rw [← ex, ← ey]
      _ = √L * (2 * (√x * √y)) := by field_simp; ring
  rw [show (↑(#X) : ℝ) * (c * √L) + ↑(#Y) * (√L / c) = c * √L * x + (√L / c) * y by ring] at htel
  rw [hbal] at htel
  rcases le_or_gt 1 δ with h1 | h1
  · have : (1 - δ) * √(m * m') ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
    exact this.trans (by positivity)
  -- `√(m m') √(|X| |Y|) ≤ |R|`
  have hR' : √(m * m') * (√x * √y) ≤ #R := by
    rw [← Real.sqrt_mul hX.le, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [mul_le_mul hRX hRY (by positivity) (by positivity)]
  have hxy : 0 < √x * √y := mul_pos (Real.sqrt_pos.2 hX) (Real.sqrt_pos.2 hY)
  have key : (1 - δ) * √(m * m') * (√x * √y) ≤ 2 * T * √L * (√x * √y) := by
    calc (1 - δ) * √(m * m') * (√x * √y) = (1 - δ) * (√(m * m') * (√x * √y)) := by ring
      _ ≤ (1 - δ) * #R := mul_le_mul_of_nonneg_left hR' (by linarith)
      _ ≤ T * (√L * (2 * (√x * √y))) := htel
      _ = 2 * T * √L * (√x * √y) := by ring
  exact le_of_mul_le_mul_right key hxy

/-- **Ambainis's adversary bound** [Ambainis2002], Theorem 2, for Boolean outputs: let a
`T`-query algorithm with a unit initial state accept, by an outcome in `S`, the first input of
every pair of a nonempty set `R` with probability at least `1 - ε` and the second with probability
at most `ε ≤ 1/2`. If every first input lies in at least `m` pairs and every second input in at
least `m'`, and for every coordinate `i` every first input lies in at most `l` pairs differing at
`i` and every second input in at most `l'`, then `(1 - 2√(ε(1-ε))) √(m m') ≤ 2T √(l l')`. The
constant is that of this proof. The source states `Ω(√(m m' / (l l')))`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (S : Finset (Fin N × Bool × W)) {R : Finset (BitString N × BitString N)}
    (hR : R.Nonempty) {ε : ℝ} (h₁ : ∀ p ∈ R, 1 - ε ≤ measureProb (run U ψ₀ p.1 T) S)
    (h₂ : ∀ p ∈ R, measureProb (run U ψ₀ p.2 T) S ≤ ε) (hε : 2 * ε ≤ 1) {m m' l l' : ℕ}
    (hm : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1}) (hm' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2})
    (hl : ∀ p ∈ R, ∀ i, #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} ≤ l)
    (hl' : ∀ p ∈ R, ∀ i, #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ l') :
    (1 - 2 * √(ε * (1 - ε))) * √(m * m') ≤ 2 * T * √(l * l') := by
  have hδ : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ 2 * √(ε * (1 - ε)) :=
    fun p hp => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
      (by rw [norm_run, hψ₀]) (h₁ p hp) (h₂ p hp) hε
  have := one_sub_mul_sqrt_le_two_mul_mul_sqrt U hψ₀ T hR hδ hm hm' (L := l * l')
    fun p hp i _ => Nat.mul_le_mul (hl p hp i) (hl' p hp i)
  simpa only [Nat.cast_mul] using this

/-- **The adversary bound across single bit flips**, the case `l = l' = 1` of [Ambainis2002],
Theorem 2, in which the related pairs are the neighbors `(x, x ⊕ eᵢ)` with `x ∈ A` and
`x ⊕ eᵢ ∈ B`: let a `T`-query algorithm with a unit initial state end, on every such pair, in
states with overlap at most `δ`. If `A` is nonempty, every input in `A` has at least `m` neighbors
in `B` and every input in `B` has at least `m'` neighbors in `A`, then `(1 - δ) √(m m') ≤ 2T`. -/
theorem one_sub_mul_sqrt_le_two_mul_of_neighbors {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) {A B : Finset (BitString N)} (hA : A.Nonempty) {δ : ℝ}
    (hδ : ∀ x ∈ A, ∀ i, update x i (!x i) ∈ B →
      ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ (update x i (!x i)) T)‖ ≤ δ) {m m' : ℕ}
    (hm : ∀ x ∈ A, m ≤ #{i | update x i (!x i) ∈ B})
    (hm' : ∀ y ∈ B, m' ≤ #{i | update y i (!y i) ∈ A}) :
    (1 - δ) * √(m * m') ≤ 2 * T := by
  classical
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · simp [h0]
  set R := hammingEdges A B
  have hflip (x : BitString N) (i : Fin N) : hammingDist x (update x i (!x i)) = 1 :=
    hammingDist_update_of_ne (by cases x i <;> simp)
  -- `R` is nonempty: some input of `A` has a neighbor in `B`
  have hR : R.Nonempty := by
    obtain ⟨x, hx⟩ := hA
    obtain ⟨i, hi⟩ := card_pos.1 (lt_of_lt_of_le hpos (hm x hx))
    exact ⟨(x, update x i (!x i)), mem_hammingEdges.2 ⟨hx, (mem_filter.1 hi).2, hflip x i⟩⟩
  -- the overlap on every related pair is at most `δ`
  have hδR : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ := by
    intro p hp
    obtain ⟨hpA, hpB, hd⟩ := mem_hammingEdges.1 hp
    obtain ⟨i, hi, -⟩ := hammingDist_eq_one_iff.1 hd
    have hp2 := (update_not_eq_of_hammingDist_le_one hd.le hi).symm
    rw [hp2] at hpB ⊢
    exact hδ p.1 hpA i hpB
  -- at most one pair from each end differs at a given coordinate
  have hl : ∀ p ∈ R, ∀ i, #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} ≤ 1 := by
    intro p _ i
    refine card_le_one.2 fun q hq r hr => ?_
    obtain ⟨hqR, hqi, hq1⟩ := mem_filter.1 hq
    obtain ⟨hrR, hri, hr1⟩ := mem_filter.1 hr
    have hq2 := (update_not_eq_of_hammingDist_le_one (mem_hammingEdges.1 hqR).2.2.le hqi).symm
    have hr2 := (update_not_eq_of_hammingDist_le_one (mem_hammingEdges.1 hrR).2.2.le hri).symm
    exact Prod.ext (hq1.trans hr1.symm) (by rw [hq2, hr2, hq1, hr1])
  have hl' : ∀ p ∈ R, ∀ i, #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ 1 := by
    intro p _ i
    refine card_le_one.2 fun q hq r hr => ?_
    obtain ⟨hqR, hqi, hq2⟩ := mem_filter.1 hq
    obtain ⟨hrR, hri, hr2⟩ := mem_filter.1 hr
    have hq1 := (update_not_eq_of_hammingDist_le_one
      ((hammingDist_comm _ _).trans (mem_hammingEdges.1 hqR).2.2).le (Ne.symm hqi)).symm
    have hr1 := (update_not_eq_of_hammingDist_le_one
      ((hammingDist_comm _ _).trans (mem_hammingEdges.1 hrR).2.2).le (Ne.symm hri)).symm
    exact Prod.ext (by rw [hq1, hr1, hq2, hr2]) (hq2.trans hr2.symm)
  -- every input has its neighbors as partners
  have hdeg : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1} := by
    intro p hp
    refine (hm p.1 (mem_hammingEdges.1 hp).1).trans (card_le_card_of_injOn
      (fun i => (p.1, update p.1 i (!p.1 i))) (fun i hi => ?_) ?_)
    · exact mem_filter.2
        ⟨mem_hammingEdges.2 ⟨(mem_hammingEdges.1 hp).1, (mem_filter.1 hi).2, hflip _ i⟩, rfl⟩
    · intro i _ j _ hij
      exact BitString.update_not_injective p.1 (congrArg Prod.snd hij)
  have hdeg' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2} := by
    intro p hp
    refine (hm' p.2 (mem_hammingEdges.1 hp).2.1).trans (card_le_card_of_injOn
      (fun i => (update p.2 i (!p.2 i), p.2)) (fun i hi => ?_) ?_)
    · refine mem_filter.2
        ⟨mem_hammingEdges.2 ⟨(mem_filter.1 hi).2, (mem_hammingEdges.1 hp).2.1, ?_⟩, rfl⟩
      rw [hammingDist_comm]
      exact hflip _ i
    · intro i _ j _ hij
      exact BitString.update_not_injective p.2 (congrArg Prod.fst hij)
  have := one_sub_mul_sqrt_le_two_mul_mul_sqrt U hψ₀ T hR hδR hdeg hdeg' (L := 1)
    fun p hp i _ => (Nat.mul_le_mul (hl p hp i) (hl' p hp i)).trans_eq (mul_one 1)
  simpa using this

/-- **The adversary bound across single bit flips**, for Boolean outputs: let a `T`-query
algorithm with a unit initial state accept every input in a nonempty set `A`, by an outcome in
`S`, with probability at least `1 - ε` and every input in `B` with probability at most `ε ≤ 1/2`.
If every input in `A` has at least `m` neighbors in `B` and every input in `B` has at least `m'`
neighbors in `A`, then `(1 - 2√(ε(1-ε))) √(m m') ≤ 2T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_of_neighbors {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {A B : Finset (BitString N)}
    (hA : A.Nonempty) {ε : ℝ} (h₁ : ∀ x ∈ A, 1 - ε ≤ measureProb (run U ψ₀ x T) S)
    (h₂ : ∀ y ∈ B, measureProb (run U ψ₀ y T) S ≤ ε) (hε : 2 * ε ≤ 1) {m m' : ℕ}
    (hm : ∀ x ∈ A, m ≤ #{i | update x i (!x i) ∈ B})
    (hm' : ∀ y ∈ B, m' ≤ #{i | update y i (!y i) ∈ A}) :
    (1 - 2 * √(ε * (1 - ε))) * √(m * m') ≤ 2 * T :=
  one_sub_mul_sqrt_le_two_mul_of_neighbors U hψ₀ T hA
    (fun x hx _ hi => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
      (by rw [norm_run, hψ₀]) (h₁ x hx) (h₂ _ hi) hε) hm hm'

end Cslib.Quantum
