/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.Extension
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.ExtensionAxiom
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.RandomGraph
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import CslibFrontier.Foundations.Analysis.SpecificLimits.DescFactorial
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Extension axioms hold almost surely

Every extension axiom holds in the binomial random graph `G(n, p)` (Mathlib's
`SimpleGraph.binomialRandom (Fin n) p`) with probability tending to `1`, for every constant
`0 < p < 1` [AlonSpencer2016, Section 10.4]. The argument is Fagin's for `p = 1/2` [Fagin1976],
with the probability that one vertex realizes a pattern bounded below. For a tuple `x` of `k`
distinct vertices and a pattern `s`, each of the `n - k` other vertices realizes `s` towards `x`
with probability at least `min (p, 1 - p) ^ k`, independently of the others
(`SimpleGraph.binomialRandom_real_forall_not_witness`). A union bound over the
`n (n - 1) ⋯ (n - k + 1)` tuples gives
`Pr[G(n, p) ⊭ EA(k, s)] ≤ n (n - 1) ⋯ (n - k + 1) · (1 - min (p, 1 - p) ^ k) ^ (n - k)`,
which tends to `0`.

At `p = 1/2`, `G(n, p)` is the uniform random graph `Cslib.Logic.FO.graph.randomGraph n`
(`Cslib.Logic.FO.graph.binomialRandom_real_eq_randomGraphProb`), and the bound becomes
`n (n - 1) ⋯ (n - k + 1) · (1 - 2⁻ᵏ) ^ (n - k)`, the bound of Fagin's proof of the `G(n, 1/2)` law
[Fagin1976] [Libkin2004, Section 12.2].

## Main results

* `Cslib.Logic.FO.graph.binomialRandom_real_not_extensionAxiom_le`: the failure bound for one
  extension axiom in `G(n, p)`.
* `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_extensionAxiom`: every extension axiom holds
  almost surely in `G(n, p)` for `0 < p < 1`.
* `Cslib.Logic.FO.graph.randomGraphProb_not_extensionAxiom_le`: the bound in `G(n, 1/2)`.
* `Cslib.Logic.FO.graph.tendsto_randomGraphProb_extensionAxiom`: each extension axiom holds in
  `G(n, 1/2)` with probability tending to `1`.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 12.2.
* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 10.4][AlonSpencer2016] (locator from
  secondary sources, unverified)
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Filter
open scoped SimpleGraph

namespace Cslib.Logic.FO.graph

/-! ### The extension axioms in `G(n, p)` -/

/-- **Failure bound for one extension axiom in `G(n, p)`.** The extension axiom for a pattern `s`
of length `k` fails in `G(n, p)` with probability at most
`n (n - 1) ⋯ (n - k + 1) · (1 - min (p, 1 - p) ^ k) ^ (n - k)`: a union bound over the tuples of
`k` distinct vertices, each failing with probability at most `(1 - min (p, 1 - p) ^ k) ^ (n - k)`
by `SimpleGraph.binomialRandom_real_forall_not_witness`. -/
theorem binomialRandom_real_not_extensionAxiom_le (p : I) (n k : ℕ) (s : Fin k → Bool) :
    G(Fin n, p).real {G | ¬Satisfies G (extensionAxiom k s)} ≤
      n.descFactorial k * (1 - min (p : ℝ) (1 - p) ^ k) ^ (n - k) := by
  classical
  set m := min (p : ℝ) (1 - p)
  have hm0 : 0 ≤ m := le_min (nonneg p) (sub_nonneg.2 (le_one p))
  -- Each tuple fails with probability at most `(1 - m ^ k) ^ (n - k)`.
  have hx : ∀ x : Fin k ↪ Fin n,
      G(Fin n, p).real {G | ∀ z, ¬((∀ i, z ≠ x i) ∧ ∀ i, (G.Adj z (x i) ↔ s i = true))} ≤
        (1 - m ^ k) ^ (n - k) := fun x => by
    rw [SimpleGraph.binomialRandom_real_forall_not_witness, Fintype.card_fin]
    have hw : ∀ i, m ≤ if s i then (p : ℝ) else 1 - p := fun i => by
      cases s i
      · exact min_le_right _ _
      · exact min_le_left _ _
    have hle : m ^ k ≤ ∏ i, (if s i then (p : ℝ) else 1 - p) := by
      calc m ^ k = ∏ _i : Fin k, m := (Fin.prod_const k m).symm
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hm0) fun i _ => hw i
    have hle1 : ∏ i, (if s i then (p : ℝ) else 1 - p) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => hm0.trans (hw i)) fun i _ => by
        cases s i
        · exact sub_le_self _ (nonneg p)
        · exact le_one p
    exact pow_le_pow_left₀ (sub_nonneg.2 hle1) (sub_le_sub_left hle 1) _
  -- The union bound over the tuples of distinct vertices.
  have hsub : {G : SimpleGraph (Fin n) | ¬Satisfies G (extensionAxiom k s)} ⊆
      ⋃ x ∈ (Finset.univ : Finset (Fin k ↪ Fin n)),
        {G | ∀ z, ¬((∀ i, z ≠ x i) ∧ ∀ i, (G.Adj z (x i) ↔ s i = true))} := by
    intro G hG
    rw [Set.mem_ofPred_eq, satisfies_extensionAxiom_iff] at hG
    push Not at hG
    obtain ⟨x, hx, hG⟩ := hG
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ ⟨x, hx⟩)) fun z ⟨hz, hadj⟩ => ?_
    obtain ⟨i, hi⟩ := hG z hz
    rcases hi with ⟨h, hs⟩ | ⟨h, hs⟩
    · exact hs ((hadj i).1 h)
    · exact h ((hadj i).2 hs)
  calc G(Fin n, p).real {G | ¬Satisfies G (extensionAxiom k s)}
      ≤ ∑ x : Fin k ↪ Fin n,
          G(Fin n, p).real {G | ∀ z, ¬((∀ i, z ≠ x i) ∧ ∀ i, (G.Adj z (x i) ↔ s i = true))} :=
        (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _x : Fin k ↪ Fin n, (1 - m ^ k) ^ (n - k) := Finset.sum_le_sum fun x _ => hx x
    _ = n.descFactorial k * (1 - m ^ k) ^ (n - k) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]

/-- **The extension axioms hold almost surely in `G(n, p)`** for every constant `0 < p < 1`
[AlonSpencer2016, Section 10.4]. -/
theorem tendsto_binomialRandom_real_extensionAxiom {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (k : ℕ) (s : Fin k → Bool) :
    Tendsto (fun n => G(Fin n, p).real {G | Satisfies G (extensionAxiom k s)}) atTop (nhds 1) := by
  have hm0 : 0 < min (p : ℝ) (1 - p) := lt_min hp0 (sub_pos.2 hp1)
  have hm1 : min (p : ℝ) (1 - p) ≤ 1 := (min_le_left _ _).trans (le_one p)
  have hq0 : 0 ≤ 1 - min (p : ℝ) (1 - p) ^ k := sub_nonneg.2 (pow_le_one₀ hm0.le hm1)
  have hq1 : 1 - min (p : ℝ) (1 - p) ^ k < 1 := sub_lt_self _ (pow_pos hm0 k)
  have hfail : Tendsto (fun n => G(Fin n, p).real {G | ¬Satisfies G (extensionAxiom k s)})
      atTop (nhds 0) :=
    squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => binomialRandom_real_not_extensionAxiom_le p n k s)
      (tendsto_descFactorial_mul_pow_sub k hq0 hq1)
  have h := hfail.const_sub 1
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  rw [← Set.compl_ofPred, probReal_compl_eq_one_sub (Set.toFinite _).measurableSet, sub_sub_cancel]

/-! ### `G(n, 1/2)` -/

/-- The edge probability `1/2`. -/
private noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem coe_half : (half : ℝ) = 1 / 2 := rfl

/-- **Extension axioms fail rarely.** The probability that `G(n, 1/2)` violates the extension
axiom for a pattern `s : Fin k → Bool` is at most
`n (n - 1) ⋯ (n - k + 1) · (1 - 2⁻ᵏ) ^ (n - k)` [Libkin2004, Section 12.2]. This is the case
`p = 1/2` of `binomialRandom_real_not_extensionAxiom_le`. -/
theorem randomGraphProb_not_extensionAxiom_le (n k : ℕ) (s : Fin k → Bool) :
    randomGraphProb n (fun G => ¬Satisfies G (extensionAxiom k s)) ≤
      n.descFactorial k * (1 - (2 ^ k : ℝ)⁻¹) ^ (n - k) := by
  have hm : min (half : ℝ) (1 - half) ^ k = (2 ^ k : ℝ)⁻¹ := by
    rw [coe_half, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, min_self, one_div, inv_pow]
  rw [← binomialRandom_real_eq_randomGraphProb coe_half, ← hm]
  exact binomialRandom_real_not_extensionAxiom_le half n k s

/-- **Extension axioms hold almost surely.** For every pattern `s`, the probability that
`G(n, 1/2)` satisfies the extension axiom for `s` tends to `1` [Fagin1976]
[Libkin2004, Section 12.2]. -/
theorem tendsto_randomGraphProb_extensionAxiom (k : ℕ) (s : Fin k → Bool) :
    Tendsto (fun n => randomGraphProb n (fun G => Satisfies G (extensionAxiom k s))) atTop
      (nhds 1) := by
  simp only [← binomialRandom_real_eq_randomGraphProb coe_half]
  exact tendsto_binomialRandom_real_extensionAxiom (by rw [coe_half]; norm_num)
    (by rw [coe_half]; norm_num) k s

end Cslib.Logic.FO.graph
