/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Karger.Contraction
public import Complexity.Algorithms.WordRAM.Karger.FastCut
import Complexity.Probability.PMF.TwoBranch

/-!
# Karger–Stein recursion as a client of the contraction specification

`fastCut` asks an oracle to contract a graph to a requested size. Its canonical handler
`contractLaw` is the law of the existing contraction client, with its graph state observed.
Two calls of the same oracle are fresh independent runs under `OracleComp.evalWith`.

Recursion decreases the explicit size parameter, not the size of an arbitrary oracle reply.
The canonical handler's support theorem establishes that replies have the requested size.
At a leaf the client returns half the doubled weight after contracting to two vertices; at a
node it returns the minimum of two recursive trials. No native execution model is introduced.

The threshold and cutoff are the existing integer choices of this formalization, documented in
`WordRAM.Karger.FastCut`: recurse at size at least seven, and choose the least integer threshold
whose cut-survival ratio is at least one half. The source is [KargerStein1996], Section 4,
Figure 6 and Lemma 4.3; this is a paraphrase, with the same documented integer deviations.

## Main definitions

* `contractLaw`: the graph law of the existing contraction client.
* `fastCut`, `fastCutLaw`: recursive oracle client and its law under that handler.

## Main results

* `fastCutLaw_leaf`, `fastCutLaw_node`: exact leaf and independent-branch equations.
* `survives_contractLaw`, `isContractionOf_of_mem_support_contractLaw`: existing contraction
  semantics transferred to the oracle's observed graph law.

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Karger

open scoped ENNReal
open Cslib.WeightedCut Cslib.Algorithms.WordRAM.Karger

/-- One oracle reply observes the graph left by the existing contraction client. -/
noncomputable def contractLaw : Graph × ℕ → PMF Graph := fun (G, target) =>
  (spec.toRandomized.withCoins.run (contractTimes (G.size - target)) G).map Prod.snd

/-- Recursive contraction with two fresh branches. The explicit size parameter decreases even
when an arbitrary oracle supplies a reply of an unrelated size. -/
def fastCut (k : ℕ) (G : Graph) : OracleComp (fun _ : Graph × ℕ => Graph) ℕ :=
  if hk : 7 ≤ k then
    have : fastCutThreshold k < k := fastCutThreshold_lt (by omega)
    do
      let first ← OracleComp.query (G, fastCutThreshold k)
      let a ← fastCut (fastCutThreshold k) first
      let second ← OracleComp.query (G, fastCutThreshold k)
      let b ← fastCut (fastCutThreshold k) second
      pure (min a b)
  else do
    let leaf ← OracleComp.query (G, 2)
    pure (totalDoubledWeight leaf.weight / 2)
termination_by k

/-- The canonical recursive answer law, using the existing contraction semantics. -/
noncomputable def fastCutLaw (k : ℕ) (G : Graph) : PMF ℕ :=
  OracleComp.evalWith contractLaw (fastCut k G)

/-- Below the recursion cutoff, contract to two vertices and read their cut value. -/
theorem fastCut_of_lt_seven {k : ℕ} (hk : k < 7) (G : Graph) :
    fastCut k G = (do
      let leaf ← OracleComp.query (G, 2)
      pure (totalDoubledWeight leaf.weight / 2)) := by
  rw [fastCut]
  simp only [show ¬7 ≤ k by omega, ↓reduceDIte]

/-- At a recursive node, each branch starts from the original graph independently. -/
theorem fastCut_of_ge_seven {k : ℕ} (hk : 7 ≤ k) (G : Graph) :
    fastCut k G = (do
      let first ← OracleComp.query (G, fastCutThreshold k)
      let a ← fastCut (fastCutThreshold k) first
      let second ← OracleComp.query (G, fastCutThreshold k)
      let b ← fastCut (fastCutThreshold k) second
      pure (min a b)) := by
  rw [fastCut]
  simp only [hk, ↓reduceDIte]

/-- A leaf has exactly the existing single-trial Karger answer law. -/
theorem fastCutLaw_leaf {k : ℕ} (hk : k < 7) (G : Graph) :
    fastCutLaw k G = answerLaw G := by
  obtain ⟨n, W⟩ := G
  rw [fastCutLaw, fastCut_of_lt_seven hk]
  simp only [OracleComp.evalWith_bind, OracleComp.evalWith_query, OracleComp.evalWith_pure]
  change (contractLaw (⟨n, W⟩, 2)).bind
    (fun G => PMF.pure (totalDoubledWeight G.weight / 2)) = _
  exact (PMF.bind_pure_comp _ _).trans (answerLaw_eq W).symm

/-- The node law is the minimum of two independent answers from the same branch law. -/
theorem fastCutLaw_node {k : ℕ} (hk : 7 ≤ k) (G : Graph) :
    fastCutLaw k G =
      let branch := (contractLaw (G, fastCutThreshold k)).bind
        fun child => fastCutLaw (fastCutThreshold k) child
      branch.bind fun a => branch.map (min a) := by
  rw [fastCutLaw, fastCut_of_ge_seven hk]
  simp only [OracleComp.evalWith_bind, OracleComp.evalWith_query, OracleComp.evalWith_pure,
    fastCutLaw]
  change ((contractLaw (G, fastCutThreshold k)).bind fun child =>
    (OracleComp.evalWith contractLaw (fastCut (fastCutThreshold k) child)).bind fun a =>
      (contractLaw (G, fastCutThreshold k)).bind fun child =>
        (OracleComp.evalWith contractLaw (fastCut (fastCutThreshold k) child)).bind fun b =>
          PMF.pure (min a b)) = _
  simp only [← PMF.bind_pure_comp, PMF.bind_bind, Function.comp_def]

/-- Contracting from `k` to `target ≥ 2` retains a fixed minimum cut with the existing exact
survival lower bound. The target remains a variable before the recursive threshold is chosen. -/
theorem survives_contractLaw {n k target : ℕ} (ht : 2 ≤ target) (htk : target ≤ k)
    {W₀ : Fin n → Fin n → ℕ} (hmin : 0 < minCut W₀)
    {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k} (hC : IsContractionOf W₀ part W)
    {B : Finset (Fin k)} (hB : IsNonTrivialCut B)
    (hBmin : cutWeight W₀ (pullbackCut part B) = minCut W₀) :
    ((target * (target - 1) : ℕ) : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞) ≤
      (contractLaw (⟨k, W⟩, target)).toOuterMeasure
        {G | Survives W₀ (pullbackCut part B) target G} := by
  obtain ⟨s, rfl⟩ : ∃ s, k = target + s := ⟨k - target, by omega⟩
  simpa only [contractLaw, Nat.add_sub_cancel_left, PMF.toOuterMeasure_map_apply,
    Set.preimage_ofPred_eq] using
    survives_contractTimes ht hmin s hC hB hBmin

/-- Every supported reply has the requested size and is a contraction of the same original
graph. In particular the canonical handler validates the size used for recursion. -/
theorem isContractionOf_of_mem_support_contractLaw {n k target : ℕ}
    (ht : 1 ≤ target) (htk : target ≤ k)
    {W₀ : Fin n → Fin n → ℕ} {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k}
    (hC : IsContractionOf W₀ part W) {G : Graph}
    (hG : G ∈ (contractLaw (⟨k, W⟩, target)).support) :
    ∃ (W' : Fin target → Fin target → ℕ) (part' : Fin n → Fin target),
      G = ⟨target, W'⟩ ∧ IsContractionOf W₀ part' W' := by
  obtain ⟨s, rfl⟩ : ∃ s, k = target + s := ⟨k - target, by omega⟩
  rw [contractLaw, Nat.add_sub_cancel_left, PMF.mem_support_map_iff] at hG
  obtain ⟨x, hx, rfl⟩ := hG
  exact isContractionOf_of_mem_support_contractTimes ht s hC hx

/-- Every recursive answer is the weight of a non-trivial cut of the original graph, including
when recursion starts from a contraction of that graph. -/
theorem exists_cut_of_mem_support_fastCutLaw {n k : ℕ} (hk : 2 ≤ k)
    {W₀ : Fin n → Fin n → ℕ} {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k}
    (hC : IsContractionOf W₀ part W) {v : ℕ}
    (hv : v ∈ (fastCutLaw k ⟨k, W⟩).support) :
    ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ v = cutWeight W₀ C := by
  have aux : ∀ k, 2 ≤ k → ∀ (W : Fin k → Fin k → ℕ) (part : Fin n → Fin k),
      IsContractionOf W₀ part W → ∀ v ∈ (fastCutLaw k ⟨k, W⟩).support,
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ v = cutWeight W₀ C := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk W part hC v hv
      by_cases hk7 : 7 ≤ k
      · rw [fastCutLaw_node hk7, PMF.mem_support_bind_iff] at hv
        obtain ⟨a, ha, hv⟩ := hv
        obtain ⟨b, hb, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
        have hbranch : ∀ v ∈ ((contractLaw (⟨k, W⟩, fastCutThreshold k)).bind
            fun child => fastCutLaw (fastCutThreshold k) child).support,
            ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ v = cutWeight W₀ C := by
          intro v hv
          obtain ⟨child, hchild, hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
          obtain ⟨W', part', rfl, hC'⟩ := isContractionOf_of_mem_support_contractLaw
            (by have := fastCutThreshold_ge_two (by omega : 4 ≤ k); omega)
            (Nat.le_of_lt (fastCutThreshold_lt (by omega))) hC hchild
          exact ih _ (fastCutThreshold_lt (by omega))
            (fastCutThreshold_ge_two (by omega)) W' part' hC' v hv
        rcases le_total a b with hab | hba
        · rw [min_eq_left hab]
          exact hbranch a ha
        · rw [min_eq_right hba]
          exact hbranch b hb
      · rw [fastCutLaw_leaf (by omega)] at hv
        obtain ⟨B, hB, hv⟩ := exists_cut_of_mem_support_answerLaw hk hC.multigraph hv
        exact ⟨pullbackCut part B, isNonTrivialCut_pullbackCut hC.surj hB,
          hv.trans (cutWeight_pullbackCut hC B).symm⟩
  exact aux k hk W part hC v hv

/-- Recursive contraction has one-sided error relative to the original graph. -/
theorem minCut_le_of_mem_support_fastCutLaw {n k : ℕ} (hk : 2 ≤ k)
    {W₀ : Fin n → Fin n → ℕ} {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k}
    (hC : IsContractionOf W₀ part W) {v : ℕ}
    (hv : v ∈ (fastCutLaw k ⟨k, W⟩).support) : minCut W₀ ≤ v := by
  obtain ⟨C, hC, rfl⟩ := exists_cut_of_mem_support_fastCutLaw hk hC hv
  exact minCut_le_cutWeight W₀ hC

/-- A single contraction trial from a contraction of the original graph retains any represented
minimum cut with the usual `2 / (k (k - 1))` lower bound. -/
theorem answerLaw_hit_prob_ge {n k : ℕ} (hk : 2 ≤ k)
    {W₀ : Fin n → Fin n → ℕ} (hmin : 0 < minCut W₀)
    {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k} (hC : IsContractionOf W₀ part W)
    {B : Finset (Fin k)} (hB : IsNonTrivialCut B)
    (hBmin : cutWeight W₀ (pullbackCut part B) = minCut W₀) :
    (2 : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞) ≤
      (answerLaw ⟨k, W⟩).toOuterMeasure {v | v = minCut W₀} := by
  rw [answerLaw_eq, PMF.toOuterMeasure_map_apply]
  have hsurv := survives_contractLaw (target := 2) le_rfl hk hmin hC hB hBmin
  refine hsurv.trans (MeasureTheory.measure_mono fun G hG => ?_)
  obtain ⟨W', part', B', rfl, hC', hpb⟩ := hG
  have hB' : IsNonTrivialCut B' :=
    isNonTrivialCut_of_pullbackCut part' (hpb ▸ isNonTrivialCut_pullbackCut hC.surj hB)
  have hcut : W' 0 1 = minCut W₀ := by
    rw [← cutWeight_fin_two hC'.multigraph hB', ← cutWeight_pullbackCut hC', hpb, hBmin]
  change totalDoubledWeight W' / 2 = minCut W₀
  rw [totalDoubledWeight_fin_two hC'.multigraph, ← hcut]
  omega

/-- A represented minimum cut is found with probability at least `2 / (d + 30)` when the
recursive depth is at most `d`. Probability reasoning concerns only the specification law. -/
theorem fastCutLaw_hit_prob_ge {n : ℕ} {W₀ : Fin n → Fin n → ℕ}
    (hmin : 0 < minCut W₀) :
    ∀ d {k : ℕ} {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k},
      2 ≤ k → fastCutDepth k ≤ d → IsContractionOf W₀ part W →
      ∀ B : Finset (Fin k), IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (2 : ℝ≥0∞) / ((d + 30 : ℕ) : ℝ≥0∞) ≤
          (fastCutLaw k ⟨k, W⟩).toOuterMeasure {v | v = minCut W₀} := by
  intro d
  induction d with
  | zero =>
    intro k W part hk hd hC B hB hBmin
    have hk7 : k < 7 := by
      by_contra h
      rw [fastCutDepth_of_ge_seven (by omega)] at hd
      omega
    rw [fastCutLaw_leaf hk7]
    exact (base_survival_ge hk (by omega)).trans (answerLaw_hit_prob_ge hk hmin hC hB hBmin)
  | succ d ih =>
    intro k W part hk hd hC B hB hBmin
    by_cases hk7 : 7 ≤ k
    · let t := fastCutThreshold k
      have ht : 2 ≤ t := fastCutThreshold_ge_two (by omega)
      have htk : t ≤ k := Nat.le_of_lt (fastCutThreshold_lt (by omega))
      have hd' : fastCutDepth t ≤ d := by
        dsimp only [t]
        rw [fastCutDepth_of_ge_seven hk7] at hd
        omega
      let branch := (contractLaw (⟨k, W⟩, t)).bind fun child => fastCutLaw t child
      have hbranch : (1 : ℝ≥0∞) / ((d + 30 : ℕ) : ℝ≥0∞) ≤
          branch.toOuterMeasure {v | v = minCut W₀} := by
        have hsurv := (half_le_threshold_survival hk7).trans
          (survives_contractLaw ht htk hmin hC hB hBmin)
        have hprod := Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal
          (contractLaw (⟨k, W⟩, t)) (fun child => fastCutLaw t child)
          {G | Survives W₀ (pullbackCut part B) t G} {v | v = minCut W₀} hsurv
          (s₂ := (2 : ℝ≥0∞) / ((d + 30 : ℕ) : ℝ≥0∞)) ?_
        · rwa [half_mul_two_div_eq (by omega : 1 ≤ d + 30)] at hprod
        · intro G _ hG
          obtain ⟨W', part', B', rfl, hC', hpb⟩ := hG
          exact ih ht hd' hC' B'
            (isNonTrivialCut_of_pullbackCut part'
              (hpb ▸ isNonTrivialCut_pullbackCut hC.surj hB)) (hpb ▸ hBmin)
      have hge : ∀ v ∈ branch.support, minCut W₀ ≤ v := by
        intro v hv
        obtain ⟨G, hG, hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
        obtain ⟨W', part', rfl, hC'⟩ :=
          isContractionOf_of_mem_support_contractLaw (by omega) htk hC hG
        exact minCut_le_of_mem_support_fastCutLaw ht hC' hv
      rw [fastCutLaw_node hk7]
      have hrec := Probability.PMF.two_branch_hit_prob_ge branch (fun _ => branch) min
        {v | v = minCut W₀} {v | v = minCut W₀} (s := d + 30) (by omega) hbranch
        (fun a _ ha b hb => by
          change a = minCut W₀ at ha
          change min a b = minCut W₀
          rw [ha, min_eq_left (hge b hb)])
        (fun a ha _ => by
          refine hbranch.trans ?_
          rw [PMF.toOuterMeasure_map_apply]
          exact MeasureTheory.measure_mono fun b hb => by
            change b = minCut W₀ at hb
            change min a b = minCut W₀
            rw [hb, min_eq_right (hge a ha)])
      exact hrec
    · rw [fastCutLaw_leaf (by omega)]
      refine le_trans ?_ ((base_survival_ge hk (by omega)).trans
        (answerLaw_hit_prob_ge hk hmin hC hB hBmin))
      apply ENNReal.div_le_div_left
      exact_mod_cast (show 30 ≤ d + 1 + 30 by omega)

/-- A single root trial finds the minimum cut with probability at least `1 / (log₂ n + 15)`.
The connectedness hypothesis is the existing positive-minimum-cut condition. -/
theorem fastCutLaw_root_hit_prob_ge {n : ℕ} (hn : 2 ≤ n)
    {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W) (hmin : 0 < minCut W) :
    (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) ≤
      (fastCutLaw n ⟨n, W⟩).toOuterMeasure {v | v = minCut W} := by
  obtain ⟨C, hC, hCmin⟩ := exists_minCut_achiever (by rw [Fintype.card_fin]; omega) W
  rw [← root_hit_prob_eq]
  exact fastCutLaw_hit_prob_ge hmin _ hn (fastCutDepth_le_two_mul_log n)
    (isContractionOf_id hW) C hC (by rw [pullbackCut_id, hCmin])

/-- The law of independent recursive trials, keeping their least answer. The trial schedule is
the existing concrete `O(log² n)` schedule; no additional native model is used. -/
noncomputable def fastCutHighProbLaw (n : ℕ) (G : Graph) : PMF ℕ :=
  OracleComp.evalWith (fun _ => fastCutLaw n G) (minRuns (fastCutTrials n))

/-- Every answer of the amplified law is still a non-trivial cut weight. -/
theorem exists_cut_of_mem_support_fastCutHighProbLaw {n : ℕ} (hn : 2 ≤ n)
    {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W) {v : ℕ}
    (hv : v ∈ (fastCutHighProbLaw n ⟨n, W⟩).support) :
    ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ v = cutWeight W C :=
  exists_cut_of_mem_support_fastCutLaw hn (isContractionOf_id hW)
    (mem_support_minRuns (by have := fastCutTrials_pos n; omega) hv)

/-- The existing independent-trial schedule misses the minimum cut with probability at most
`1 / (2 n)`. The bound is for the recursive specification's answer law. -/
theorem fastCutHighProbLaw_failure_le {n : ℕ} (hn : 2 ≤ n)
    {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W) (hmin : 0 < minCut W) :
    (fastCutHighProbLaw n ⟨n, W⟩).toOuterMeasure {v | v ≠ minCut W} ≤
      (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞) := by
  have hmiss := Probability.PMF.toOuterMeasure_compl_le_one_sub _ _
    (fastCutLaw_root_hit_prob_ge hn hW hmin)
  exact (minRuns_ne_le
    (fun _ hv => minCut_le_of_mem_support_fastCutLaw hn (isContractionOf_id hW) hv)
    hmiss (fastCutTrials n)).trans (fastCutHighProb_failure_le n)

/-- Updating a previously valid least answer cannot increase a trial's failure probability.
The first trial ignores the initial least-answer word. This is a law of the specification. -/
theorem fastCutLaw_update_failure_le {n : ℕ} (hn : 2 ≤ n)
    {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W) (hmin : 0 < minCut W)
    (i b : ℕ) (hb : 0 < i → minCut W ≤ b) :
    ((fastCutLaw n ⟨n, W⟩).map (fun v => if i = 0 then v else min v b)).toOuterMeasure
        {v | v ≠ minCut W} ≤
      (1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) := by
  have hmiss := Probability.PMF.toOuterMeasure_compl_le_one_sub _ _
    (fastCutLaw_root_hit_prob_ge hn hW hmin)
  refine le_trans ?_ hmiss
  rw [PMF.toOuterMeasure_map_apply]
  refine MeasureTheory.measure_mono fun v hv => ?_
  change (if i = 0 then v else min v b) ≠ minCut W at hv
  change v ≠ minCut W
  intro heq
  apply hv
  by_cases hi : i = 0
  · simp only [hi, ↓reduceIte, heq]
  · simp only [hi, ↓reduceIte, heq, min_eq_left (hb (Nat.pos_of_ne_zero hi))]

end Cslib.Algorithms.Lean.Karger
