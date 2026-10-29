/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.LabelCover
public import Complexity.Computability.PCP.Approximation.Hastad.LinearTest
import Complexity.Foundations.Data.Finset.Average
import Complexity.Foundations.Data.Finset.Expect

/-!
# Håstad's 3-bit linear test: soundness against Label Cover

Håstad [Hastad2001] proved that, for every `ε > 0`, it is NP-hard to satisfy more than a
`7 / 8 + ε` fraction of the clauses of a satisfiable E3-CNF formula, matching the random-assignment
bound `Cslib.Logic.PL.CNF.IsExactThreeDistinct.unsatVal_le_one_eighth`. Together with its submodule
`LinearTest`, this module formalizes the analytic core of that proof, the completeness and
soundness of Håstad's noisy 3-bit linear test on folded Long Code tables over a Label Cover
projection `π : β → γ`. It does not prove the hardness result: no reduction to MAX-E3LIN or
MAX-E3SAT is constructed, and NP-hardness of Label Cover (the PCP theorem with parallel repetition)
is not formalized.

1. The **Long Code** of `x : α` (`Cslib.BitString.longCode`) evaluates each Boolean function
   `g : α → Bool` at `x`. A table `B : (γ → Bool) → Bool` is **folded**, that is, odd
   (`Cslib.BitString.IsOdd`), when `B (f + fun _ => true) = !B f`, which kills the empty Fourier
   coefficient `fourierCoeff (signVal ∘ B) ∅ = 0` (`Cslib.BitString.IsOdd.fourierCoeff_empty`).
2. Given an edge projection `π : β → γ`, a right table `B : (γ → Bool) → Bool`, and a left table
   `A : (β → Bool) → Bool`, **Håstad's 3-bit linear test** samples uniform `f : γ → Bool` and
   `g : β → Bool`, a `δ`-biased noise function `μ : β → Bool`, and checks whether
   `B f ^^ A g = A ((f ∘ π) + g + μ)`.
3. On valid Long Code tables `B = longCode (π x)` and `A = longCode x`, the linear test accepts with
   probability `1 - δ` (`Cslib.PCP.Hastad.linearProb_longCode`).
4. By Walsh–Fourier inversion, the test correlation `linearCorr π δ B A` equals
   `∑ T : Finset β, (1 - 2 * δ) ^ #T * fourierCoeff (signVal ∘ B) (projectSet π T) *
     fourierCoeff (signVal ∘ A) T ^ 2`
   (`Cslib.PCP.Hastad.linearCorr_eq_sum`). Splitting at degree `k` and applying
   Cauchy–Schwarz and Parseval's identity bounds `(linearCorr π δ B A) ^ 2` by
   `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * ∑ x, spectralWeight k A x * spectralWeight k B (π x)`
   (`Cslib.PCP.Hastad.linearCorr_sq_le`), where `spectralWeight k A` is a sub-probability
   distribution on `β`.
5. Decoding the spectral weights into a labelling bounds the average correlation over a Label Cover
   instance by its value (`Cslib.PCP.Hastad.graphLinearCorr_sq_le`).

## Main definitions

* `Cslib.PCP.Hastad.graphLinearCorr`, `Cslib.PCP.Hastad.graphLinearProb`: multi-edge
  test averages over a Label Cover instance.

## Main results

* `Cslib.PCP.Hastad.exists_labelling_of_spectralWeight`: spectral decoding of Label Cover tables.
* `Cslib.PCP.Hastad.graphLinearCorr_sq_le`: multi-edge Cauchy–Schwarz + Parseval soundness
  bound.
* `Cslib.PCP.Hastad.gapLabelCover_dichotomy_lt_one`: for every `ε` and `δ` there is a
  threshold `0 < η < 1`,
  independent of the label sets, such that on `GapLabelCover` yes-instances some folded tables pass
  the 3-bit test with probability `1 - δ`, and on no-instances every folded table passes with
  probability at most `1 / 2 + 4 * ε`.

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
* [R. O'Donnell, *Analysis of Boolean Functions*, Chapter 7][ODonnell2014]
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Cslib.PCP.Hastad

open Cslib.BitString Cslib.Complexity Cslib.PCP.Encoded

/-! ### Multi-edge Label Cover decoding and soundness -/

section LabelCoverSoundness

/-- Any deterministic labelling `(ℓ, r)` of a Label Cover instance `g` satisfies at most
`g.edges.length * (1 - (g.toGraph projectionEval).unsatVal)` edges. -/
private theorem sum_satisfies_le_unsatVal {β γ : Type} [DecidableEq γ]
    (g : Graph (β → γ)) (ℓ : ℕ → β) (r : ℕ → γ) :
    (∑ i : Fin g.edges.length,
      if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = r (g.edges.get i).dst then (1 : ℝ)
      else 0) ≤
    g.edges.length * (1 - (g.toGraph projectionEval).unsatVal) := by
  let σ : ℕ → β × γ := fun v => (ℓ v, r v)
  have hcompl (i : Fin g.edges.length) :
      (if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = r (g.edges.get i).dst then (1 : ℝ)
        else 0) +
      (if i ∈ (g.toGraph projectionEval).unsatEdges σ then (1 : ℝ) else 0) = 1 := by
    simp only [ConstraintGraph.mem_unsatEdges, satisfies_toGraph_projectionEval_iff, σ]
    split_ifs <;> ring
  have hsum :
      (∑ i : Fin g.edges.length,
        if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = r (g.edges.get i).dst then (1 : ℝ)
        else 0) +
      #((g.toGraph projectionEval).unsatEdges σ) = g.edges.length := by
    have h1 := sum_congr (s₁ := univ) rfl (fun i _ => hcompl i)
    have h2 :
        (∑ i : Fin g.edges.length,
          if i ∈ (g.toGraph projectionEval).unsatEdges σ then (1 : ℝ) else 0) =
        #((g.toGraph projectionEval).unsatEdges σ) := by
      rw [sum_boole, filter_mem_eq_inter, univ_inter]
    rw [sum_add_distrib, h2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
    exact h1
  have hcard := (g.toGraph projectionEval).card_mul_unsatFrac σ
  simp only [Fintype.card_fin] at hcard
  have hle : (g.edges.length : ℝ) * (g.toGraph projectionEval).unsatVal ≤
      #((g.toGraph projectionEval).unsatEdges σ) := by
    rw [← hcard]
    exact mul_le_mul_of_nonneg_left ((g.toGraph projectionEval).unsatVal_le σ) (Nat.cast_nonneg _)
  linarith

variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ]

/-- **Spectral decoding of Label Cover tables**: for any Label Cover instance `g : Graph (β → γ)`,
degree cutoff `k`, left tables `A`, and right tables `B`, there exist deterministic labellings
`ℓ : ℕ → β` and `r : ℕ → γ` whose number of satisfied edges is at least the total spectral weight
agreement across all edges of `g`. -/
theorem exists_labelling_of_spectralWeight (g : Graph (β → γ)) (k : ℕ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) :
    ∃ (ℓ : ℕ → β) (r : ℕ → γ),
      (∑ i : Fin g.edges.length, ∑ x : β,
        spectralWeight k (A (g.edges.get i).src) x *
          spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x)) ≤
      ∑ i : Fin g.edges.length,
        if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = r (g.edges.get i).dst then 1
        else 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_choice_sum_le
    (fun i : Fin g.edges.length => (g.edges.get i).src)
    (fun i x => spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x))
    (fun i x => spectralWeight_nonneg k _ _)
    (fun u x => spectralWeight k (A u) x)
    (fun u x => spectralWeight_nonneg k _ _)
    (fun u => sum_spectralWeight_le_one k (A u))
  obtain ⟨r, hr⟩ := exists_choice_sum_le
    (fun i : Fin g.edges.length => (g.edges.get i).dst)
    (fun i y => if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = y then (1 : ℝ) else 0)
    (fun i y => by split_ifs <;> positivity)
    (fun w y => spectralWeight k (B w) y)
    (fun w y => spectralWeight_nonneg k _ _)
    (fun w => sum_spectralWeight_le_one k (B w))
  refine ⟨ℓ, r, hℓ.trans (le_trans ?_ hr)⟩
  refine le_of_eq (sum_congr rfl fun i _ => ?_)
  simp [mul_ite, mul_one, mul_zero, sum_ite_eq]

/-- Total spectral weight agreement across the edges of a Label Cover instance `g` is at most
`g.edges.length * (1 - (g.toGraph projectionEval).unsatVal)`. -/
private theorem sum_spectralWeight_le_unsatVal (g : Graph (β → γ)) (k : ℕ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) :
    (∑ i : Fin g.edges.length, ∑ x : β,
      spectralWeight k (A (g.edges.get i).src) x *
        spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x)) ≤
    g.edges.length * (1 - (g.toGraph projectionEval).unsatVal) := by
  obtain ⟨ℓ, r, hℓr⟩ := exists_labelling_of_spectralWeight g k B A
  exact hℓr.trans (sum_satisfies_le_unsatVal g ℓ r)

/-- Average correlation of Håstad's 3-bit linear test across the edges of a Label Cover instance
`g : Graph (β → γ)`. -/
noncomputable def graphLinearCorr (g : Graph (β → γ)) (δ : ℝ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) : ℝ :=
  𝔼 i : Fin g.edges.length,
    linearCorr (g.edges.get i).constraint δ (B (g.edges.get i).dst) (A (g.edges.get i).src)

/-- Average acceptance probability of Håstad's 3-bit linear test across the edges of a Label Cover
instance `g : Graph (β → γ)`. -/
noncomputable def graphLinearProb (g : Graph (β → γ)) (δ : ℝ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) : ℝ :=
  𝔼 i : Fin g.edges.length,
    linearProb (g.edges.get i).constraint δ (B (g.edges.get i).dst) (A (g.edges.get i).src)

omit [Nonempty β] [Nonempty γ] in
/-- For a Label Cover instance with at least one edge,
`graphLinearProb g δ B A = 1 / 2 + 1 / 2 * graphLinearCorr g δ B A`. -/
private theorem graphLinearProb_eq_add_graphLinearCorr {g : Graph (β → γ)}
    (hg : g.edges ≠ []) (δ : ℝ) (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) :
    graphLinearProb g δ B A = 1 / 2 + 1 / 2 * graphLinearCorr g δ B A := by
  have hne : (univ : Finset (Fin g.edges.length)).Nonempty :=
    univ_nonempty_iff.2 ⟨⟨0, List.length_pos_of_ne_nil hg⟩⟩
  simp only [graphLinearProb, graphLinearCorr, linearProb_eq_add_linearCorr,
    expect_add_distrib, expect_const hne, ← mul_expect]

omit [Nonempty β] [Nonempty γ] in
/-- **Multi-edge completeness of Håstad's tests**: if `(ℓ, r)` satisfies every edge of a non-empty
Label Cover instance `g`, then the Long Code tables `B w = longCode (r w)` and
`A u = longCode (ℓ u)` are folded and achieve linear acceptance `1 - δ`. -/
theorem graphLinearProb_longCode_of_satisfies {g : Graph (β → γ)} (hg : g.edges ≠ []) (δ : ℝ)
    {ℓ : ℕ → β} {r : ℕ → γ} (hℓr : ∀ d ∈ g.edges, d.constraint (ℓ d.src) = r d.dst) :
    (∀ w, IsOdd (longCode (r w))) ∧
      graphLinearProb g δ (fun w => longCode (r w)) (fun u => longCode (ℓ u)) = 1 - δ := by
  have hne : (univ : Finset (Fin g.edges.length)).Nonempty :=
    univ_nonempty_iff.2 ⟨⟨0, List.length_pos_of_ne_nil hg⟩⟩
  refine ⟨fun w => isOdd_longCode (r w), ?_⟩
  unfold graphLinearProb
  have hterm (i : Fin g.edges.length) :
      linearProb (g.edges.get i).constraint δ
        (longCode (r (g.edges.get i).dst)) (longCode (ℓ (g.edges.get i).src)) = 1 - δ := by
    rw [← hℓr (g.edges.get i) (List.get_mem _ _), linearProb_longCode]
  simp only [hterm, expect_const hne]

/-- **Multi-edge soundness bound for Håstad's 3-bit test over Label Cover**
[Håstad, Theorem 5.6][Hastad2001]: for any Label Cover instance `g : Graph (β → γ)`, noise rate
`0 ≤ δ ≤ 1 / 2`, degree cutoff `k`, folded right tables `B`, and left tables `A`, the squared
average correlation `graphLinearCorr g δ B A ^ 2` is at most
`(1 - 2 * δ) ^ (2 * k) + k ^ 2 * (1 - (g.toGraph projectionEval).unsatVal)`. -/
theorem graphLinearCorr_sq_le (g : Graph (β → γ)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (k : ℕ) {B : ℕ → (γ → Bool) → Bool} (hB : ∀ w, IsOdd (B w))
    (A : ℕ → (β → Bool) → Bool) :
    graphLinearCorr g δ B A ^ 2 ≤
      (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * (1 - (g.toGraph projectionEval).unsatVal) := by
  have hρ0 : 0 ≤ 1 - 2 * δ := by linarith
  have hunsat1 : (g.toGraph projectionEval).unsatVal ≤ 1 :=
    (g.toGraph projectionEval).unsatVal_le_one
  rcases g.edges.eq_nil_or_concat with hnil | ⟨l, d, hconcat⟩
  · have hempty : IsEmpty (Fin g.edges.length) := by simp [hnil]
    rw [show graphLinearCorr g δ B A = 0 by simp [graphLinearCorr], sq, mul_zero]
    positivity
  · have hm_pos : (0 : ℝ) < g.edges.length := by
      rw [hconcat, List.length_concat]
      positivity
    refine (sq_expect_le_expect_sq univ _).trans ?_
    rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_le_iff₀ hm_pos]
    calc (∑ i : Fin g.edges.length,
          linearCorr (g.edges.get i).constraint δ
            (B (g.edges.get i).dst) (A (g.edges.get i).src) ^ 2)
      _ ≤ ∑ i : Fin g.edges.length,
            ((1 - 2 * δ) ^ (2 * k) +
              (k : ℝ) ^ 2 * ∑ x : β,
                spectralWeight k (A (g.edges.get i).src) x *
                  spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x)) :=
        sum_le_sum fun i _ =>
          linearCorr_sq_le (g.edges.get i).constraint hδ0 hδ1 k
            (hB (g.edges.get i).dst) (A (g.edges.get i).src)
      _ = g.edges.length * (1 - 2 * δ) ^ (2 * k) +
            (k : ℝ) ^ 2 * ∑ i : Fin g.edges.length, ∑ x : β,
              spectralWeight k (A (g.edges.get i).src) x *
                spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x) := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
      _ ≤ g.edges.length * (1 - 2 * δ) ^ (2 * k) +
            (k : ℝ) ^ 2 * (g.edges.length * (1 - (g.toGraph projectionEval).unsatVal)) := by
        gcongr
        exact sum_spectralWeight_le_unsatVal g k B A
      _ = ((1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * (1 - (g.toGraph projectionEval).unsatVal)) *
            g.edges.length := by ring

/-- When a Label Cover instance `g` has maximum satisfied edge fraction
`1 - (g.toGraph projectionEval).unsatVal ≤ η` and `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * η ≤ (8 * ε) ^ 2`
(`0 ≤ ε`), every assignment of folded right tables `B` and left tables `A` has average linear
correlation at most `8 * ε`. -/
private theorem graphLinearCorr_le_of_unsatVal (g : Graph (β → γ)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (k : ℕ) {η ε : ℝ} (hε : 0 ≤ ε)
    (hη : 1 - (g.toGraph projectionEval).unsatVal ≤ η)
    (hparam : (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * η ≤ (8 * ε) ^ 2)
    {B : ℕ → (γ → Bool) → Bool} (hB : ∀ w, IsOdd (B w)) (A : ℕ → (β → Bool) → Bool) :
    graphLinearCorr g δ B A ≤ 8 * ε := by
  have hsq : graphLinearCorr g δ B A ^ 2 ≤ (8 * ε) ^ 2 := by
    calc graphLinearCorr g δ B A ^ 2
      _ ≤ (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * (1 - (g.toGraph projectionEval).unsatVal) :=
        graphLinearCorr_sq_le g hδ0 hδ1 k hB A
      _ ≤ (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * η := by gcongr
      _ ≤ (8 * ε) ^ 2 := hparam
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- For every `ε > 0` and `0 < δ < 1 / 2`, there exist a degree cutoff `k : ℕ` and a Label Cover
soundness threshold `η > 0` such that `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * η ≤ (8 * ε) ^ 2`. -/
private theorem exists_params {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ (k : ℕ) (η : ℝ), 0 < η ∧ (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * η ≤ (8 * ε) ^ 2 := by
  have hρ0 : 0 ≤ 1 - 2 * δ := by linarith
  have hρ1 : 1 - 2 * δ < 1 := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < (8 * ε) ^ 2 / 2) hρ1
  refine ⟨N + 1, (8 * ε) ^ 2 / (2 * ((N + 1 : ℕ) : ℝ) ^ 2), by positivity, ?_⟩
  have hpow : (1 - 2 * δ) ^ (2 * (N + 1)) ≤ (1 - 2 * δ) ^ N :=
    pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
  have hmul : ((N + 1 : ℕ) : ℝ) ^ 2 * ((8 * ε) ^ 2 / (2 * ((N + 1 : ℕ) : ℝ) ^ 2)) =
      (8 * ε) ^ 2 / 2 := by
    have hpos : ((N + 1 : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  linarith

end LabelCoverSoundness

/-- **Completeness and soundness of Håstad's 3-bit linear test against Label Cover**
[Håstad, Theorem 5.6][Hastad2001]:
for every `ε > 0` and `0 < δ < 1 / 2`, there exists a Label Cover soundness parameter `0 < η < 1`,
independent of the label sets `β` and `γ`, such that for every Label Cover instance
`g : Graph (β → γ)` with `g.edges ≠ []`:
1. (**Completeness**) If `g ∈ (GapLabelCover β γ 1 η).yes`, there exist folded tables `B` and `A`
   achieving `graphLinearProb g δ B A = 1 - δ`.
2. (**Soundness**) If `g ∈ (GapLabelCover β γ 1 η).no`, then for all folded right tables `B` and
   all left tables `A`, `graphLinearProb g δ B A ≤ 1 / 2 + 4 * ε`.

This is the analytic core of Håstad's MAX-E3LIN hardness proof. It is not a reduction: no
instance of MAX-E3LIN or MAX-E3SAT is constructed, and NP-hardness of `GapLabelCover` is not
proved here. The threshold is strictly below the completeness value, as required by the
no-instance promise. This does not assert that no-instances exist for every fixed pair of label
sets; sufficiently large label sets can be required. -/
theorem gapLabelCover_dichotomy_lt_one {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β]
      [Fintype γ] [DecidableEq γ] [Nonempty γ] {g : Graph (β → γ)}, g.edges ≠ [] →
      (g ∈ (GapLabelCover β γ 1 η).yes →
        ∃ (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool),
          (∀ w, IsOdd (B w)) ∧
            graphLinearProb g δ B A = 1 - δ) ∧
      (g ∈ (GapLabelCover β γ 1 η).no →
        ∀ (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool),
          (∀ w, IsOdd (B w)) →
            graphLinearProb g δ B A ≤ 1 / 2 + 4 * ε) := by
  obtain ⟨k, θ, hθ, hparam⟩ := exists_params hε hδ0 hδ1
  let η := min θ (1 / 2)
  have hη : 0 < η := lt_min hθ (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hparam' : (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * η ≤ (8 * ε) ^ 2 :=
    (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (min_le_left θ (1 / 2)) (sq_nonneg (k : ℝ)))).trans hparam
  refine ⟨η, hη, hη1, fun {β γ} _ _ _ _ _ _ {g} hg => ⟨?_, ?_⟩⟩
  · intro hyes
    simp only [GapLabelCover, PromiseProblem.mem_yes_gapMax] at hyes
    have hunsat0 : (g.toGraph projectionEval).unsatVal = 0 :=
      le_antisymm (by linarith) (g.toGraph projectionEval).unsatVal_nonneg
    have hsat : (g.toGraph projectionEval).Satisfiable :=
      (g.toGraph projectionEval).unsatVal_eq_zero_iff.1 hunsat0
    obtain ⟨ℓ, r, hℓr⟩ := (satisfiable_toGraph_projectionEval_iff g).1 hsat
    obtain ⟨hfold, hlin⟩ := graphLinearProb_longCode_of_satisfies hg δ hℓr
    exact ⟨fun w => longCode (r w), fun u => longCode (ℓ u), hfold, hlin⟩
  · intro hno B A hB
    simp only [GapLabelCover, PromiseProblem.mem_no_gapMax] at hno
    have hcorr := graphLinearCorr_le_of_unsatVal g hδ0.le hδ1.le k hε.le hno.1 hparam' hB A
    have hlin := graphLinearProb_eq_add_graphLinearCorr hg δ B A
    linarith

/-- Compatibility form of `gapLabelCover_dichotomy_lt_one`, retaining the original public
statement. Use the stronger theorem when a nontrivial Label Cover gap is needed. -/
theorem gapLabelCover_dichotomy {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β]
      [Fintype γ] [DecidableEq γ] [Nonempty γ] {g : Graph (β → γ)}, g.edges ≠ [] →
      (g ∈ (GapLabelCover β γ 1 η).yes →
        ∃ (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool),
          (∀ w, IsOdd (B w)) ∧
            graphLinearProb g δ B A = 1 - δ) ∧
      (g ∈ (GapLabelCover β γ 1 η).no →
        ∀ (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool),
          (∀ w, IsOdd (B w)) →
            graphLinearProb g δ B A ≤ 1 / 2 + 4 * ε) := by
  obtain ⟨η, hη, _, h⟩ := gapLabelCover_dichotomy_lt_one hε hδ0 hδ1
  exact ⟨η, hη, h⟩

end Cslib.PCP.Hastad
