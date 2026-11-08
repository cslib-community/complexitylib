/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Karger.Contraction
public import Complexity.Foundations.Combinatorics.WeightedCut.Blocks
import Complexity.Probability.PMF.Map

/-!
# Each minimum cut is output with probability at least `1 / C(n, 2)`

The contraction structure `Cslib.Algorithms.Lean.Karger.spec` keeps only the weight matrix of the
current supervertices, so a run of `karger` answers a weight but not a cut. Following
[Karger and Stein, Section 2][KargerStein1996], the structure `trackedSpec n` also keeps, for each
supervertex, the block of original vertices merged into it (`TrackedGraph`, contracted by
`Cslib.WeightedCut.contractBlocks`). The blocks are bookkeeping: every client with coins draws the
same answers and the same weight matrices over `trackedSpec n` as over `spec`
(`map_run_trackedSpec`). One run of `karger` over `trackedSpec n` therefore also outputs a cut,
the block of the second of the two supervertices it leaves (`TrackedGraph.side`), whose law is
`cutLaw W₀`. Its answer is the weight of that cut (`answer_eq_cutWeight_side`,
`answerLaw_eq_map_cutLaw`).

A cut survives the contractions exactly when it is the preimage of a cut of the contracted graph
(`TrackedSurvives`), and a cut that survives down to two supervertices is the output cut, up to
complement. The survival bound of `Cslib.Algorithms.Lean.Karger.survives_contractTimes`, rerun
over the blocks (`trackedSurvives_contractTimes`), gives Karger's theorem for a fixed minimum cut:
`karger` outputs it with probability at least `2 / (n (n - 1)) = 1 / C(n, 2)`
(`two_div_le_cutLaw`). Since each run outputs one cut, the events for distinct minimum cuts are
disjoint, so there are at most `C(n, 2)` minimum cuts (`card_minCuts_le_choose_two`).

Source map ([KargerStein1996], author copy dated 6 August 1996):

* Section 2, the blocks `s(a)` and the output cut `(s(a), s(b))`: `TrackedGraph`,
  `TrackedGraph.side`.
* Lemma 2.1, "a cut is output iff no edge crossing it is contracted": the direction used, a cut
  that survives is output, is `two_div_le_cutLaw`'s final step, with `TrackedSurvives` for
  "no crossing edge was contracted".
* Theorem 2.2, a particular minimum cut is output with probability at least `C(n, 2)⁻¹`:
  `two_div_le_cutLaw`.
* The count of minimum cuts, attributed in the proof of Theorem 4.4 to Dinitz, Karzanov and
  Lomonosov (1976): `card_minCuts_le_choose_two`, by the disjointness argument of the proof of
  Theorem 8.4 (stated there for `α`-minimal cuts) applied to Theorem 2.2. The `n`-cycle attains
  it (`ComplexityTests.KargerMinCutCount`).

Scope: weights are natural numbers (`Cslib.WeightedCut.IsMultigraph`), and the graph is connected
(`0 < minCut W₀`), without which the count fails (the empty graph on four vertices has seven
minimum cuts). A minimum cut `{C, Cᶜ}` is counted once, by its side `C` that avoids a fixed vertex
`x₀`. Not formalized here: the `O(n^(2α))` bound on `α`-minimal cuts (Theorem 8.4), the cactus
representation of all minimum cuts, and the per-cut bound for the recursive Karger–Stein
algorithm.

## Main definitions

* `TrackedGraph`, `contractTracked`, `trackedStep`, `trackedSpec`: the contraction structure with
  blocks.
* `TrackedSurvives`: a cut of the input survives in a contraction with blocks.
* `TrackedGraph.side`, `cutLaw`: the cut that one run of `karger` outputs, and its law.

## Main results

* `map_run_trackedSpec`: forgetting the blocks maps runs over `trackedSpec n` to runs over `spec`.
* `trackedSurvives_contractTimes`: the survival bound, over the blocks.
* `answer_eq_cutWeight_side`, `answerLaw_eq_map_cutLaw`: the answer is the weight of the
  non-trivial output cut.
* `two_div_le_cutLaw`: each minimum cut is output with probability at least `2 / (n (n - 1))`.
* `card_minCuts_le_choose_two`: at most `n.choose 2` minimum cuts.

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

public section

namespace Cslib.Algorithms.Lean.Karger

open scoped ENNReal
open Cslib.WeightedCut Cslib.Algorithms.WordRAM.Karger Cslib.DataStructure

/-! ## The contraction structure with blocks -/

/-- A contraction of a multigraph on `Fin n`: the weight matrix on `size` supervertices, and the
block of original vertices merged into each supervertex. -/
structure TrackedGraph (n : ℕ) where
  /-- The number of supervertices. -/
  size : ℕ
  /-- The weight matrix. -/
  weight : Fin size → Fin size → ℕ
  /-- The original vertices merged into each supervertex. -/
  blocks : Fin size → Finset (Fin n)

/-- The graph of a tracked contraction, forgetting the blocks. -/
def TrackedGraph.toGraph {n : ℕ} (G : TrackedGraph n) : Graph := ⟨G.size, G.weight⟩

/-- The singleton blocks of the uncontracted graph `W`. -/
def TrackedGraph.init {n : ℕ} (W : Fin n → Fin n → ℕ) : TrackedGraph n :=
  ⟨n, W, fun i => pullbackCut id {i}⟩

/-- Contraction with blocks: `contractGraph` on the weights, and `contractBlocks` on the blocks.
Arguments out of range leave the graph unchanged. -/
def contractTracked {n : ℕ} : TrackedGraph n → ℕ → ℕ → TrackedGraph n
  | ⟨k + 1, W, b⟩, u, v =>
    if h : u < k + 1 ∧ v < k + 1 then
      ⟨k, contractMatrix W ⟨u, h.1⟩ ⟨v, h.2⟩, contractBlocks b ⟨u, h.1⟩ ⟨v, h.2⟩⟩
    else ⟨k + 1, W, b⟩
  | G, _, _ => G

/-- Contraction with blocks at a pair of supervertices in range. -/
theorem contractTracked_fin {n m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ)
    (b : Fin (m + 1) → Finset (Fin n)) (u v : Fin (m + 1)) :
    contractTracked ⟨m + 1, W, b⟩ u v = ⟨m, contractMatrix W u v, contractBlocks b u v⟩ := by
  rw [contractTracked, dite_eq_left ⟨u.isLt, v.isLt⟩]

private theorem contractTracked_of_lt {n k u v : ℕ} (W : Fin (k + 1) → Fin (k + 1) → ℕ)
    (b : Fin (k + 1) → Finset (Fin n)) (h : u < k + 1 ∧ v < k + 1) :
    contractTracked ⟨k + 1, W, b⟩ u v =
      ⟨k, contractMatrix W ⟨u, h.1⟩ ⟨v, h.2⟩, contractBlocks b ⟨u, h.1⟩ ⟨v, h.2⟩⟩ := by
  rw [contractTracked, dite_eq_left h]

private theorem contractTracked_of_not_lt {n k u v : ℕ} (W : Fin (k + 1) → Fin (k + 1) → ℕ)
    (b : Fin (k + 1) → Finset (Fin n)) (h : ¬(u < k + 1 ∧ v < k + 1)) :
    contractTracked ⟨k + 1, W, b⟩ u v = ⟨k + 1, W, b⟩ := by
  rw [contractTracked, dite_eq_right h]

/-- Forgetting the blocks commutes with contraction. -/
theorem toGraph_contractTracked {n : ℕ} (G : TrackedGraph n) (u v : ℕ) :
    (contractTracked G u v).toGraph = contractGraph G.toGraph u v := by
  obtain ⟨_ | k, W, b⟩ := G
  · rfl
  · change _ = contractGraph ⟨k + 1, W⟩ u v
    by_cases h : u < k + 1 ∧ v < k + 1
    · rw [contractTracked_of_lt W b h, contractGraph, dite_eq_left h]
      rfl
    · rw [contractTracked_of_not_lt W b h, contractGraph, dite_eq_right h]
      rfl

/-- The transition function of the contraction structure with blocks: `step` on the weights. -/
noncomputable def trackedStep {n : ℕ} (G : TrackedGraph n) : (o : Op) → TrackedGraph n × o.Result
  | .size => (G, G.size)
  | .total => (G, totalDoubledWeight G.weight)
  | .pairAt r => (G, sampledPair G.weight r)
  | .contract u v => (contractTracked G u v, ())

/-- The contraction structure with blocks: the operations of `spec`, with the same answers. -/
noncomputable abbrev trackedSpec (n : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (trackedStep (n := n)) fun G o => valid G.toGraph o

/-- The steps of the two structures agree on the graph. -/
theorem trackedStep_toGraph {n : ℕ} (G : TrackedGraph n) (o : Op) :
    ((trackedStep G o).1.toGraph, (trackedStep G o).2) = step G.toGraph o := by
  cases o with
  | size => rfl
  | total => rfl
  | pairAt r => rfl
  | contract u v => exact Prod.ext (toGraph_contractTracked G u v) rfl

/-! ## Runs -/

/-- **The blocks are bookkeeping.** Every client with coins draws the same answers and the same
graphs over the structure with blocks as over `spec`. -/
theorem map_run_trackedSpec {n : ℕ} {α : Type} (p : ProbOracleComp Op.Result α)
    (G : TrackedGraph n) :
    ((trackedSpec n).toRandomized.withCoins.run p G).map (fun x => (x.1, x.2.toGraph)) =
      spec.toRandomized.withCoins.run p G.toGraph := by
  induction p generalizing G with
  | pure a => simp
  | liftBind o k ih =>
    rw [RandomizedSpec.run_liftBind, RandomizedSpec.run_liftBind, PMF.map_bind]
    cases o with
    | inl m =>
      rw [RandomizedSpec.withCoins_law_inl, RandomizedSpec.withCoins_law_inl, PMF.bind_map,
        PMF.bind_map]
      exact congrArg _ (funext fun r => ih r G)
    | inr o =>
      change (PMF.pure ((trackedStep G o).2, (trackedStep G o).1)).bind _ =
        (PMF.pure ((step G.toGraph o).2, (step G.toGraph o).1)).bind _
      rw [PMF.pure_bind, PMF.pure_bind, ← trackedStep_toGraph G o]
      exact ih _ _

/-- One contraction of a graph with positive total weight, over the structure with blocks: a
uniform offset below the total doubled weight, then contraction of the pair sampled there. -/
theorem run_tracked_contractStep_bind {n : ℕ} {α : Type} (p : ProbOracleComp Op.Result α) {m : ℕ}
    (W : Fin (m + 1) → Fin (m + 1) → ℕ) (b : Fin (m + 1) → Finset (Fin n))
    (hS : totalDoubledWeight W ≠ 0) :
    (trackedSpec n).toRandomized.withCoins.run (contractStep >>= fun _ => p) ⟨m + 1, W, b⟩ =
      (ProbComp.unifOracle (totalDoubledWeight W - 1)).bind fun r =>
        (trackedSpec n).toRandomized.withCoins.run p
          (contractTracked ⟨m + 1, W, b⟩ (sampledPair W r).1 (sampledPair W r).2) := by
  simp only [contractStep, bind_assoc]
  rw [StateTransitionSpec.run_withCoins_query_bind, StateTransitionSpec.run_withCoins_query_bind]
  dsimp only [StateTransitionSpec.stepFn, trackedStep]
  simp only [hS, ite_false, bind_assoc]
  rw [RandomizedSpec.withCoins_run_sample_bind, ProbComp.eval_unifFin]
  refine congrArg _ (funext fun r => ?_)
  rw [StateTransitionSpec.run_withCoins_query_bind, StateTransitionSpec.run_withCoins_query_bind]
  rfl

/-- One contraction of a weightless graph contracts its first and last supervertices. -/
theorem run_tracked_contractStep_bind_of_eq_zero {n : ℕ} {α : Type}
    (p : ProbOracleComp Op.Result α) {m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ)
    (b : Fin (m + 1) → Finset (Fin n)) (hS : totalDoubledWeight W = 0) :
    (trackedSpec n).toRandomized.withCoins.run (contractStep >>= fun _ => p) ⟨m + 1, W, b⟩ =
      (trackedSpec n).toRandomized.withCoins.run p
        ⟨m, contractMatrix W 0 (Fin.last m), contractBlocks b 0 (Fin.last m)⟩ := by
  simp only [contractStep, bind_assoc]
  rw [StateTransitionSpec.run_withCoins_query_bind, StateTransitionSpec.run_withCoins_query_bind]
  dsimp only [StateTransitionSpec.stepFn, trackedStep]
  simp only [hS, ite_true]
  rw [StateTransitionSpec.run_withCoins_query_bind]
  exact congrArg _ (contractTracked_fin W b 0 (Fin.last m))

/-- Every outcome of `s` contractions of a contraction of `W₀` from `t + s ≥ 2` supervertices,
with the fibres of its map as blocks, is a contraction of `W₀` to `t` supervertices with the fibres
of its map as blocks. -/
theorem exists_of_mem_support_tracked_contractTimes {n t : ℕ} (ht : 1 ≤ t)
    {W₀ : Fin n → Fin n → ℕ} (s : ℕ) {W : Fin (t + s) → Fin (t + s) → ℕ}
    {part : Fin n → Fin (t + s)} (hC : IsContractionOf W₀ part W) {x : Unit × TrackedGraph n}
    (hx : x ∈ ((trackedSpec n).toRandomized.withCoins.run (contractTimes s)
      ⟨t + s, W, fun i => pullbackCut part {i}⟩).support) :
    ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
      x.2 = ⟨t, W', fun i => pullbackCut part' {i}⟩ ∧ IsContractionOf W₀ part' W' := by
  induction s with
  | zero =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
    exact ⟨W, part, rfl, hC⟩
  | succ s ih =>
    change x ∈ ((trackedSpec n).toRandomized.withCoins.run
      (contractStep >>= fun _ => contractTimes s)
      ⟨t + s + 1, W, fun i => pullbackCut part {i}⟩).support at hx
    by_cases hS : totalDoubledWeight W = 0
    · rw [run_tracked_contractStep_bind_of_eq_zero (m := t + s) _ W _ hS] at hx
      have h0 : (0 : Fin (t + s + 1)) ≠ Fin.last (t + s) := by
        rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        omega
      erw [contractBlocks_pullbackCut part h0] at hx
      exact ih (isContractionOf_contract hC h0) hx
    · rw [run_tracked_contractStep_bind (m := t + s) _ W _ hS, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      obtain ⟨u, v, hsamp⟩ := exists_isSampledPair W (show (r : ℕ) < totalDoubledWeight W by
        have := r.isLt
        omega)
      have huv : u ≠ v := isSampledPair_ne hC.multigraph hsamp
      rw [sampledPair_eq hsamp, contractTracked_fin] at hx
      erw [contractBlocks_pullbackCut part huv] at hx
      exact ih (isContractionOf_contract hC huv) hx

/-- The cut `C` of `W₀` survives in `G`: `G` is a contraction of `W₀` to `t` supervertices along
a map whose fibres are the blocks of `G`, under which `C` is the preimage of a cut. -/
def TrackedSurvives {n : ℕ} (W₀ : Fin n → Fin n → ℕ) (C : Finset (Fin n)) (t : ℕ)
    (G : TrackedGraph n) : Prop :=
  ∃ (W : Fin t → Fin t → ℕ) (part : Fin n → Fin t) (B : Finset (Fin t)),
    G = ⟨t, W, fun i => pullbackCut part {i}⟩ ∧ IsContractionOf W₀ part W ∧
      pullbackCut part B = C

/-- **Survival of a minimum cut, over the blocks** [KargerStein1996]. Contracting a contraction
of a connected multigraph `W₀` from `t + s` down to `t ≥ 2` supervertices, with the fibres of its
map as blocks, preserves a fixed minimum cut with probability at least
`t (t - 1) / ((t + s) (t + s - 1))`. -/
theorem trackedSurvives_contractTimes {n t : ℕ} (ht : 2 ≤ t) {W₀ : Fin n → Fin n → ℕ}
    (hmin : 0 < minCut W₀) (s : ℕ) {W : Fin (t + s) → Fin (t + s) → ℕ}
    {part : Fin n → Fin (t + s)} (hC : IsContractionOf W₀ part W) {B : Finset (Fin (t + s))}
    (hB : IsNonTrivialCut B) (hBmin : cutWeight W₀ (pullbackCut part B) = minCut W₀) :
    ((t * (t - 1) : ℕ) : ℝ≥0∞) / (((t + s) * (t + s - 1) : ℕ) : ℝ≥0∞) ≤
      ((trackedSpec n).toRandomized.withCoins.run (contractTimes s)
        ⟨t + s, W, fun i => pullbackCut part {i}⟩).toOuterMeasure
        {x | TrackedSurvives W₀ (pullbackCut part B) t x.2} := by
  induction s with
  | zero =>
    have hpos : ((t * (t - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (by omega) (by omega)).ne'
    change ((t * (t - 1) : ℕ) : ℝ≥0∞) / ((t * (t - 1) : ℕ) : ℝ≥0∞) ≤
      (PMF.pure ((), (⟨t, W, fun i => pullbackCut part {i}⟩ : TrackedGraph n))).toOuterMeasure _
    rw [ENNReal.div_self hpos (ENNReal.natCast_ne_top _), PMF.toOuterMeasure_pure_apply,
      ite_eq_left ⟨W, part, B, rfl, hC, rfl⟩]
  | succ s ih =>
    have hcard : 2 ≤ Fintype.card (Fin (t + s + 1)) := by rw [Fintype.card_fin]; omega
    have hminW : minCut W₀ ≤ minCut W := minCut_le_of_isContractionOf hcard hC
    have hS : 0 < totalDoubledWeight W :=
      totalDoubledWeight_pos_of_minCut_pos hcard hC.multigraph (lt_of_lt_of_le hmin hminW)
    change _ ≤ ((trackedSpec n).toRandomized.withCoins.run
      (contractStep >>= fun _ => contractTimes s)
      ⟨t + s + 1, W, fun i => pullbackCut part {i}⟩).toOuterMeasure _
    rw [run_tracked_contractStep_bind (m := t + s) _ W _ hS.ne',
      show (t + (s + 1)) * (t + (s + 1) - 1) = (t + s + 1) * (t + s) by
        rw [show t + (s + 1) - 1 = t + s by omega]; rfl,
      ← telescope_survival_step ht (show t ≤ t + s by omega)]
    let castFin : Fin (totalDoubledWeight W - 1 + 1) ≃ Fin (totalDoubledWeight W) :=
      finCongr (by omega)
    have hdeg : (t + s + 1) * cutWeight W B ≤ totalDoubledWeight W := by
      have hmul := mul_minCut_le_totalDoubledWeight hcard hC.multigraph
      rw [Fintype.card_fin] at hmul
      rw [← cutWeight_pullbackCut hC B, hBmin]
      exact (Nat.mul_le_mul_left _ hminW).trans hmul
    have hstep : ((t + s - 1 : ℕ) : ℝ≥0∞) / (t + s + 1 : ℕ) ≤
        (ProbComp.unifOracle (totalDoubledWeight W - 1)).toOuterMeasure
          {r | SampleSurvives W B (castFin r)} := by
      have : Nonempty (Fin (totalDoubledWeight W)) := ⟨⟨0, hS⟩⟩
      have h := step_survival_prob_ge (by omega) hC.multigraph hS hdeg
      rw [show t + (s + 1) - 2 = t + s - 1 by omega,
        ← Probability.PMF.uniformOfFintype_map_equiv castFin,
        PMF.toOuterMeasure_map_apply] at h
      exact h
    refine Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal _ _ _ _ hstep fun r _ hr => ?_
    obtain ⟨u, v, hsamp, hsame⟩ := hr
    have hsamp : IsSampledPair W r u v := hsamp
    have huv : u ≠ v := isSampledPair_ne hC.multigraph hsamp
    have hpb := pullbackCut_contractCut part huv hsame
    have hnt : IsNonTrivialCut (contractCut v B) :=
      isNonTrivialCut_of_pullbackCut _ (hpb ▸ isNonTrivialCut_pullbackCut hC.surj hB)
    rw [sampledPair_eq hsamp, contractTracked_fin]
    erw [contractBlocks_pullbackCut part huv]
    rw [← hpb]
    exact ih (isContractionOf_contract hC huv) hnt (hpb ▸ hBmin)

/-! ## The output cut -/

/-- The cut that a tracked contraction to two supervertices outputs: the block of supervertex
`1`. -/
def TrackedGraph.side {n : ℕ} (G : TrackedGraph n) : Finset (Fin n) :=
  if h : 1 < G.size then G.blocks ⟨1, h⟩ else ∅

/-- Running `karger` on the structure with blocks contracts `n - 2` times, then answers half the
total weight. -/
private theorem run_karger_tracked {n : ℕ} (W : Fin n → Fin n → ℕ) :
    (trackedSpec n).toRandomized.withCoins.run karger (TrackedGraph.init W) =
      ((trackedSpec n).toRandomized.withCoins.run (contractTimes (n - 2))
        (TrackedGraph.init W)).bind fun x =>
        PMF.pure (totalDoubledWeight x.2.weight / 2, x.2) := by
  rw [karger, StateTransitionSpec.run_withCoins_query_bind]
  dsimp only [StateTransitionSpec.stepFn, trackedStep]
  rw [RandomizedSpec.run_bind]
  exact congrArg _ (funext fun ⟨_, G⟩ =>
    StateTransitionSpec.run_withCoins_query_bind (D := trackedSpec n) Op.total
      (fun S => pure (S / 2)) G)

/-- The law of the cut that one run of `karger` outputs on `W`: the block of the second of the two
supervertices it leaves. -/
noncomputable def cutLaw {n : ℕ} (W : Fin n → Fin n → ℕ) : PMF (Finset (Fin n)) :=
  ((trackedSpec n).toRandomized.withCoins.run karger (TrackedGraph.init W)).map
    fun x => x.2.side

/-- The output cut is the block of supervertex `1` after `n - 2` contractions. -/
theorem cutLaw_eq {n : ℕ} (W : Fin n → Fin n → ℕ) :
    cutLaw W = ((trackedSpec n).toRandomized.withCoins.run (contractTimes (n - 2))
      (TrackedGraph.init W)).map fun x => x.2.side := by
  rw [cutLaw, run_karger_tracked, PMF.map_bind]
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- **The answer is the weight of the output cut.** Every outcome of `karger` on a multigraph with
`n ≥ 2` vertices, over the structure with blocks, outputs a non-trivial cut `side` and answers its
weight. -/
theorem answer_eq_cutWeight_side {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) {x : ℕ × TrackedGraph n}
    (hx : x ∈ ((trackedSpec n).toRandomized.withCoins.run karger
      (TrackedGraph.init W₀)).support) :
    IsNonTrivialCut x.2.side ∧ x.1 = cutWeight W₀ x.2.side := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 + s := ⟨n - 2, by omega⟩
  rw [run_karger_tracked, PMF.mem_support_bind_iff] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [PMF.mem_support_pure_iff] at hx
  subst hx
  rw [Nat.add_sub_cancel_left] at hy
  obtain ⟨W', part', hy', hC'⟩ := exists_of_mem_support_tracked_contractTimes (t := 2)
    (by norm_num) s (isContractionOf_id hW₀) hy
  have h1 : IsNonTrivialCut ({1} : Finset (Fin 2)) := isNonTrivialCut_singleton (by simp) 1
  have hside : y.2.side = pullbackCut part' {1} := by rw [hy']; rfl
  refine ⟨hside ▸ isNonTrivialCut_pullbackCut hC'.surj h1, ?_⟩
  change totalDoubledWeight y.2.weight / 2 = cutWeight W₀ y.2.side
  rw [hside, cutWeight_pullbackCut hC', cutWeight_fin_two hC'.multigraph h1, hy']
  change totalDoubledWeight W' / 2 = W' 0 1
  rw [totalDoubledWeight_fin_two hC'.multigraph]
  omega

/-- The answer of `karger` on a multigraph with `n ≥ 2` vertices is the weight of the cut it
outputs: its law is the image of `cutLaw` under `cutWeight`. -/
theorem answerLaw_eq_map_cutLaw {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) : answerLaw ⟨n, W₀⟩ = (cutLaw W₀).map (cutWeight W₀) := by
  rw [answerLaw, show (⟨n, W₀⟩ : Graph) = (TrackedGraph.init W₀).toGraph from rfl,
    ← map_run_trackedSpec, PMF.map_comp, cutLaw, PMF.map_comp]
  exact Probability.PMF.map_congr_on_support _ _ _ fun x hx =>
    (answer_eq_cutWeight_side hn hW₀ hx).2

/-- Every cut that `karger` outputs on a multigraph with `n ≥ 2` vertices is non-trivial. -/
theorem isNonTrivialCut_of_mem_support_cutLaw {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) {C : Finset (Fin n)} (hC : C ∈ (cutLaw W₀).support) :
    IsNonTrivialCut C := by
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hC
  exact (answer_eq_cutWeight_side hn hW₀ hx).1

/-- **Karger's theorem for a fixed cut** [KargerStein1996]. On a connected multigraph with
`n ≥ 2` vertices, `karger` outputs a fixed minimum cut `{C, Cᶜ}` with probability at least
`2 / (n (n - 1)) = 1 / C(n, 2)`. -/
theorem two_div_le_cutLaw {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ} (hW₀ : IsMultigraph W₀)
    (hmin : 0 < minCut W₀) {C : Finset (Fin n)} (hC : IsNonTrivialCut C)
    (hCmin : cutWeight W₀ C = minCut W₀) :
    (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
      (cutLaw W₀).toOuterMeasure {C, Finset.univ \ C} := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 + s := ⟨n - 2, by omega⟩
  have hid : pullbackCut id C = C := pullbackCut_id C
  have hsurv := trackedSurvives_contractTimes le_rfl hmin s (isContractionOf_id hW₀)
    (B := C) hC (by rw [hid, hCmin])
  rw [hid] at hsurv
  rw [cutLaw_eq, PMF.toOuterMeasure_map_apply, Nat.add_sub_cancel_left,
    show (2 : ℝ≥0∞) / ((2 + s) * (2 + s - 1) : ℕ) =
      ((2 * (2 - 1) : ℕ) : ℝ≥0∞) / ((2 + s) * (2 + s - 1) : ℕ) by norm_num]
  refine le_trans hsurv (PMF.toOuterMeasure_mono _ ?_)
  rintro x ⟨⟨W', part', B', hx, -, hpb⟩, -⟩
  have hB' : IsNonTrivialCut B' := isNonTrivialCut_of_pullbackCut part' (hpb ▸ hC)
  rw [isNonTrivialCut_iff_card, Fintype.card_fin] at hB'
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp (show B'.card = 1 by omega)
  change x.2.side ∈ ({C, Finset.univ \ C} : Set (Finset (Fin (2 + s))))
  rw [hx]
  change pullbackCut part' {1} ∈ ({C, Finset.univ \ C} : Set (Finset (Fin (2 + s))))
  match b, hpb with
  | 0, hpb =>
    refine Or.inr ?_
    rw [show ({1} : Finset (Fin 2)) = Finset.univ \ {0} by decide, pullbackCut_compl, hpb]
    exact Set.mem_singleton _
  | 1, hpb => exact Or.inl hpb

/-- **At most `C(n, 2)` minimum cuts** [KargerStein1996]. A connected multigraph on `Fin n` has at
most `n.choose 2` minimum cuts: at most `n.choose 2` vertex sets `C` with `x₀ ∉ C` and
`cutWeight W₀ C = minCut W₀`. Each such `C` is a non-trivial cut, since `0 < minCut W₀`, and each
minimum cut `{C, Cᶜ}` has exactly one side without `x₀`. The bound is due to Dinitz, Karzanov and
Lomonosov (1976); this is the proof of [KargerStein1996], from the disjointness of the events
that `karger` outputs each minimum cut. -/
theorem card_minCuts_le_choose_two {n : ℕ} {W₀ : Fin n → Fin n → ℕ} (hW₀ : IsMultigraph W₀)
    (hmin : 0 < minCut W₀) (x₀ : Fin n) :
    (Finset.univ.filter fun C : Finset (Fin n) =>
      x₀ ∉ C ∧ cutWeight W₀ C = minCut W₀).card ≤ n.choose 2 := by
  set F := Finset.univ.filter fun C : Finset (Fin n) => x₀ ∉ C ∧ cutWeight W₀ C = minCut W₀
  have hnt : ∀ C ∈ F, IsNonTrivialCut C := by
    intro C hC
    obtain ⟨-, hx₀, hcw⟩ := Finset.mem_filter.mp hC
    refine ⟨Finset.nonempty_iff_ne_empty.mpr fun h => ?_, fun h => hx₀ (h ▸ Finset.mem_univ x₀)⟩
    have h0 : cutWeight W₀ ∅ = 0 := by simp [cutWeight]
    rw [h, h0] at hcw
    omega
  rcases F.eq_empty_or_nonempty with hF | ⟨C₁, hC₁⟩
  · rw [hF, Finset.card_empty]
    exact Nat.zero_le _
  have hn : 2 ≤ n := by
    have := (isNonTrivialCut_iff_card C₁).mp (hnt C₁ hC₁)
    rw [Fintype.card_fin] at this
    omega
  have hpair : ∀ C ∈ F, (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
      cutLaw W₀ C + cutLaw W₀ (Finset.univ \ C) := by
    intro C hC
    have hx₀ := (Finset.mem_filter.mp hC).2.1
    have hne : C ≠ Finset.univ \ C := fun h =>
      hx₀ (h ▸ Finset.mem_sdiff.mpr ⟨Finset.mem_univ x₀, hx₀⟩)
    have h := two_div_le_cutLaw hn hW₀ hmin (hnt C hC) (Finset.mem_filter.mp hC).2.2
    rwa [← Finset.coe_pair, PMF.toOuterMeasure_apply_finset, Finset.sum_pair hne] at h
  have hdisj : Disjoint F (F.image (Finset.univ \ ·)) := by
    rw [Finset.disjoint_left]
    intro C hC hC'
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC'
    exact (Finset.mem_filter.mp hC).2.1
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hD).2.1⟩)
  have hinj : Set.InjOn (Finset.univ \ ·) (F : Set (Finset (Fin n))) := by
    intro D₁ _ D₂ _ h
    have := congrArg (Finset.univ \ ·) h
    simpa using this
  have hsum : ∑ C ∈ F, (cutLaw W₀ C + cutLaw W₀ (Finset.univ \ C)) ≤ 1 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_image (f := fun C => cutLaw W₀ C) hinj,
      ← Finset.sum_union hdisj]
    calc ∑ C ∈ F ∪ F.image (Finset.univ \ ·), cutLaw W₀ C ≤ ∑' C, cutLaw W₀ C :=
          sum_le_tsum _
      _ = 1 := PMF.tsum_coe _
  have hle : (F.card : ℝ≥0∞) * ((2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ≤ 1 := by
    calc (F.card : ℝ≥0∞) * ((2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞))
        = ∑ _C ∈ F, (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ C ∈ F, (cutLaw W₀ C + cutLaw W₀ (Finset.univ \ C)) := Finset.sum_le_sum hpair
      _ ≤ 1 := hsum
  have hpos : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (by omega) (by omega)).ne'
  rw [← mul_div_assoc, ENNReal.div_le_iff hpos (ENNReal.natCast_ne_top _), one_mul] at hle
  have hnat : F.card * 2 ≤ n * (n - 1) := by exact_mod_cast hle
  rw [Nat.choose_two_right]
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr hnat

end Cslib.Algorithms.Lean.Karger
