/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Karger.Graph
public import Complexity.DataStructure.StateTransition.Randomized
public import Complexity.Languages.Probabilistic.Iteration

/-!
# Karger's contraction algorithm as a randomized client

Karger's contraction algorithm [Karger1993] [KargerStein1996] keeps a weighted multigraph on its
current supervertices. It repeatedly picks an edge with probability proportional to its weight
and contracts it. Here the multigraph is an abstract data type, the contraction structure `spec`,
whose state is the weight matrix of the current supervertices (`Graph`) and whose operations are
deterministic:

* `size` and `total` answer the number of supervertices and the total doubled weight `S`;
* `pairAt r` answers the pair `(u, v)` whose interval of the prefix sums of the weights contains
  the offset `r < S` (`sampledPair`, the single-draw sampling of `Karger.Graph`);
* `contract u v` merges `v` into `u` and moves the last supervertex into slot `v`
  (`contractMatrix`).

The algorithm is a client with private coins, a `ProbOracleComp Op.Result` program, run against
`spec.toRandomized.withCoins`. Each step draws a uniform offset below `S`, asks for the pair there
and contracts it (`contractStep`), so it contracts each edge `{u, v}` with probability
`2 W u v / S`. `contractTimes s` makes `s` steps, and `karger` contracts down to two supervertices
and answers half their total weight, the weight of the cut between them.

All probability is proved here, on the specification. Contracting from `t + s` down to `t`
supervertices preserves a fixed minimum cut with probability at least
`t (t - 1) / ((t + s) (t + s - 1))` (`survives_contractTimes`), so `karger` answers the minimum cut
weight with probability at least `2 / (n (n - 1))` (`two_div_le_toOuterMeasure_karger`), and every
answer is the weight of a non-trivial cut (`exists_cut_of_mem_support_answerLaw`), never less than
the minimum (`minCut_le_of_mem_support_karger`). Every call it makes is admissible
(`demonicValid_karger`). The combinatorics and the one-step bound are `Karger.Graph`'s
(`isContractionOf_contract`, `pullbackCut_contractCut`, `step_survival_prob_ge`,
`telescope_survival_step`), used unchanged, and the composition of the stages is
`Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal`.

Amplification is a client of a trial oracle whose one call answers one run of `karger`:
`minRuns R` makes `R` calls and keeps the least answer, one `minStep` per call after the first.
Answered by independent runs, `OracleComp.evalWith (fun _ => answerLaw G)`, it misses the minimum
cut weight with probability at most `(1 - 2 / (n (n - 1))) ^ R` (`minRuns_ne_minCut_le`), since
the least answer misses it only when every run does (`minRuns_ne_le`, for any trial).

No register, address or instruction count appears here. The word-RAM loop
`Cslib.Algorithms.WordRAM.Karger.contractDownTo` simulates `contractTimes`: the graph it holds has
the law of the client's final state (`Cslib.Algorithms.WordRAM.Karger.contractDownTo_law`), so its
survival bound is `survives_contractTimes`. The programs of `Cslib.Algorithms.WordRAM.KargerMinCut`
simulate `karger` and `minRuns` in the same way. An implementation of `spec` over the memory
oracle is a separate, deterministic hop, and `Refinement.toRandomized` with
`RandomizedRefinement.withCoins` carries the law of the client through it.

## Main definitions

* `Graph`, `Op`, `step`, `valid`, `spec`: the contraction structure.
* `sampledPair`, `contractGraph`: the pair sampled at an offset, and contraction.
* `contractStep`, `contractTimes`, `karger`: the algorithm as a client with coins.
* `answerLaw`: the law of the answer of one run of `karger`.
* `minStep`, `minRuns`: amplification, as a client of a trial oracle.
* `Survives`: a cut of the input survives in a contracted graph.

## Main results

* `run_contractStep_bind`, `run_contractStep_bind_of_eq_zero`: the run of one contraction, the
  step that an implementation simulates.
* `survives_contractTimes`: the survival bound.
* `two_div_le_toOuterMeasure_karger`: Karger's success probability.
* `isContractionOf_of_mem_support_contractTimes`, `exists_cut_of_mem_support_answerLaw`,
  `minCut_le_of_mem_support_karger`: every outcome is a contraction, so the answer is the weight
  of a non-trivial cut, never below the minimum.
* `answerLaw_eq`: the answer is half the total weight of the graph left by `n - 2` contractions.
* `minRuns_ne_minCut_le`: amplified Karger, `R` independent runs miss with probability at most
  `(1 - 2 / (n (n - 1))) ^ R`.
* `mem_support_iterate_minStep`, `mem_support_minRuns`: every amplified answer is the answer of
  one of the runs.
* `minRuns_ne_le`: amplification of any trial whose answers are at least `m`.
* `isCostBounded_contractStep`, `isCostBounded_contractTimes`: each contraction makes one coin
  call and at most four calls of the structure.
* `demonicValid_contractTimes`, `demonicValid_karger`: every call is admissible.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Karger

open scoped ENNReal
open Cslib.WeightedCut Cslib.Algorithms.WordRAM.Karger Cslib.DataStructure

/-! ## The contraction structure -/

/-- A weighted multigraph on `size` supervertices, given by its weight matrix. -/
structure Graph where
  /-- The number of supervertices. -/
  size : ℕ
  /-- The weight matrix. -/
  weight : Fin size → Fin size → ℕ

/-- The operations of the contraction structure. -/
inductive Op where
  /-- The number of supervertices. -/
  | size
  /-- The total doubled weight, the sum of the weighted degrees. -/
  | total
  /-- The pair sampled at offset `r` of the prefix sums of the weights. -/
  | pairAt (r : ℕ)
  /-- Merge supervertex `v` into `u`. -/
  | contract (u v : ℕ)

/-- The answer type of each operation. -/
abbrev Op.Result : Op → Type
  | .size => ℕ
  | .total => ℕ
  | .pairAt _ => ℕ × ℕ
  | .contract _ _ => Unit

open Classical in
/-- The pair sampled at offset `r`: the pair `(u, v)` whose interval of the prefix sums of the
weights contains `r` (`IsSampledPair`), or `(0, 0)` if there is none. -/
noncomputable def sampledPair {k : ℕ} (W : Fin k → Fin k → ℕ) (r : ℕ) : ℕ × ℕ :=
  if h : ∃ p : Fin k × Fin k, IsSampledPair W r p.1 p.2 then
    Prod.map Fin.val Fin.val (Classical.choose h)
  else (0, 0)

/-- Contraction: merge `v` into `u` and move the last supervertex into slot `v`
(`contractMatrix`). Arguments out of range leave the graph unchanged. -/
def contractGraph : Graph → ℕ → ℕ → Graph
  | ⟨k + 1, W⟩, u, v =>
    if h : u < k + 1 ∧ v < k + 1 then ⟨k, contractMatrix W ⟨u, h.1⟩ ⟨v, h.2⟩⟩ else ⟨k + 1, W⟩
  | G, _, _ => G

/-- The transition function of the contraction structure. -/
noncomputable def step (G : Graph) : (o : Op) → Graph × o.Result
  | .size => (G, G.size)
  | .total => (G, totalDoubledWeight G.weight)
  | .pairAt r => (G, sampledPair G.weight r)
  | .contract u v => (contractGraph G u v, ())

/-- Admissibility: an offset below the total weight, and two distinct supervertices. -/
def valid (G : Graph) : Op → Prop
  | .pairAt r => r < totalDoubledWeight G.weight
  | .contract u v => u < G.size ∧ v < G.size ∧ u ≠ v
  | _ => True

/-- The contraction structure. -/
noncomputable abbrev spec : StateTransitionSpec := StateTransitionSpec.ofFn step valid

/-- The pair sampled at an offset is the unique pair whose interval contains it. -/
theorem sampledPair_eq {k : ℕ} {W : Fin k → Fin k → ℕ} {r : ℕ} {u v : Fin k}
    (h : IsSampledPair W r u v) : sampledPair W r = ((u : ℕ), (v : ℕ)) := by
  have hex : ∃ p : Fin k × Fin k, IsSampledPair W r p.1 p.2 := ⟨(u, v), h⟩
  obtain ⟨hu, hv⟩ := isSampledPair_unique W (Classical.choose_spec hex) h
  rw [sampledPair, dite_eq_left hex, ← hu, ← hv]
  rfl

/-- Contracting two supervertices in range is `contractMatrix`. -/
theorem contractGraph_fin {m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ) (u v : Fin (m + 1)) :
    contractGraph ⟨m + 1, W⟩ u v = ⟨m, contractMatrix W u v⟩ := by
  rw [contractGraph, dite_eq_left ⟨u.isLt, v.isLt⟩]

/-! ## The algorithm -/

/-- A call of the contraction structure, in a program with coins. -/
abbrev call (o : Op) : ProbOracleComp Op.Result o.Result := ProbOracleComp.query o

/-- One contraction: draw a uniform offset below the total weight, and contract the pair sampled
there. A weightless graph contracts its first and last supervertices. -/
noncomputable def contractStep : ProbOracleComp Op.Result Unit := do
  let k ← call .size
  let S ← call .total
  if S = 0 then call (.contract 0 (k - 1)) else do
    let r ← ProbOracleComp.sample (ProbComp.unifFin (S - 1))
    let (u, v) ← call (.pairAt r)
    call (.contract u v)

/-- Contract `s` times. -/
noncomputable def contractTimes : ℕ → ProbOracleComp Op.Result Unit
  | 0 => pure ()
  | s + 1 => do
    contractStep
    contractTimes s

/-- **Karger's algorithm**: contract down to two supervertices, and answer the weight between
them, half their total weight. -/
noncomputable def karger : ProbOracleComp Op.Result ℕ := do
  let k ← call .size
  contractTimes (k - 2)
  let S ← call .total
  pure (S / 2)

/-! ## Runs -/

/-- One contraction of a graph of positive weight draws a uniform offset below the weight and
contracts the pair sampled there. -/
theorem run_contractStep_bind {α : Type} (p : ProbOracleComp Op.Result α) {m : ℕ}
    (W : Fin (m + 1) → Fin (m + 1) → ℕ) (hS : totalDoubledWeight W ≠ 0) :
    spec.toRandomized.withCoins.run (contractStep >>= fun _ => p) ⟨m + 1, W⟩ =
      (ProbComp.unifOracle (totalDoubledWeight W - 1)).bind fun r =>
        spec.toRandomized.withCoins.run p
          (contractGraph ⟨m + 1, W⟩ (sampledPair W r).1 (sampledPair W r).2) := by
  simp only [contractStep, bind_assoc]
  rw [StateTransitionSpec.run_withCoins_query_bind, StateTransitionSpec.run_withCoins_query_bind]
  dsimp only [StateTransitionSpec.stepFn, step]
  simp only [hS, ite_false, bind_assoc]
  rw [RandomizedSpec.withCoins_run_sample_bind, ProbComp.eval_unifFin]
  refine congrArg _ (funext fun r => ?_)
  rw [StateTransitionSpec.run_withCoins_query_bind, StateTransitionSpec.run_withCoins_query_bind]
  rfl

/-- One contraction of a weightless graph contracts its first and last supervertices. -/
theorem run_contractStep_bind_of_eq_zero {α : Type} (p : ProbOracleComp Op.Result α)
    {m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ) (hS : totalDoubledWeight W = 0) :
    spec.toRandomized.withCoins.run (contractStep >>= fun _ => p) ⟨m + 1, W⟩ =
      spec.toRandomized.withCoins.run p ⟨m, contractMatrix W 0 (Fin.last m)⟩ := by
  simp only [contractStep, bind_assoc]
  rw [StateTransitionSpec.run_withCoins_query_bind, StateTransitionSpec.run_withCoins_query_bind]
  dsimp only [StateTransitionSpec.stepFn, step]
  simp only [hS, ite_true]
  rw [StateTransitionSpec.run_withCoins_query_bind]
  exact congrArg _ (contractGraph_fin W 0 (Fin.last m))

/-! ## Survival of a minimum cut -/

/-- The cut `C` of `W₀` survives in `G`: `G` is a contraction of `W₀` to `t` supervertices along
some map, under which `C` is the preimage of a cut. -/
def Survives {n : ℕ} (W₀ : Fin n → Fin n → ℕ) (C : Finset (Fin n)) (t : ℕ) (G : Graph) : Prop :=
  ∃ (W : Fin t → Fin t → ℕ) (part : Fin n → Fin t) (B : Finset (Fin t)),
    G = ⟨t, W⟩ ∧ IsContractionOf W₀ part W ∧ pullbackCut part B = C

/-- **Survival of a minimum cut** [KargerStein1996]. Contracting a contraction of a connected
multigraph `W₀` from `t + s` down to `t ≥ 2` supervertices preserves a fixed minimum cut with
probability at least `t (t - 1) / ((t + s) (t + s - 1))`. -/
theorem survives_contractTimes {n t : ℕ} (ht : 2 ≤ t) {W₀ : Fin n → Fin n → ℕ}
    (hmin : 0 < minCut W₀) (s : ℕ) {W : Fin (t + s) → Fin (t + s) → ℕ}
    {part : Fin n → Fin (t + s)} (hC : IsContractionOf W₀ part W) {B : Finset (Fin (t + s))}
    (hB : IsNonTrivialCut B) (hBmin : cutWeight W₀ (pullbackCut part B) = minCut W₀) :
    ((t * (t - 1) : ℕ) : ℝ≥0∞) / (((t + s) * (t + s - 1) : ℕ) : ℝ≥0∞) ≤
      (spec.toRandomized.withCoins.run (contractTimes s) ⟨t + s, W⟩).toOuterMeasure
        {x | Survives W₀ (pullbackCut part B) t x.2} := by
  induction s with
  | zero =>
    have hpos : ((t * (t - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (by omega) (by omega)).ne'
    change ((t * (t - 1) : ℕ) : ℝ≥0∞) / ((t * (t - 1) : ℕ) : ℝ≥0∞) ≤
      (PMF.pure ((), (⟨t, W⟩ : Graph))).toOuterMeasure _
    rw [ENNReal.div_self hpos (ENNReal.natCast_ne_top _), PMF.toOuterMeasure_pure_apply,
      ite_eq_left ⟨W, part, B, rfl, hC, rfl⟩]
  | succ s ih =>
    have hcard : 2 ≤ Fintype.card (Fin (t + s + 1)) := by rw [Fintype.card_fin]; omega
    have hminW : minCut W₀ ≤ minCut W := minCut_le_of_isContractionOf hcard hC
    have hS : 0 < totalDoubledWeight W :=
      totalDoubledWeight_pos_of_minCut_pos hcard hC.multigraph (lt_of_lt_of_le hmin hminW)
    change _ ≤ (spec.toRandomized.withCoins.run (contractStep >>= fun _ => contractTimes s)
      ⟨t + s + 1, W⟩).toOuterMeasure _
    rw [run_contractStep_bind (m := t + s) _ W hS.ne',
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
    rw [sampledPair_eq hsamp, contractGraph_fin, ← hpb]
    exact ih (isContractionOf_contract hC huv) hnt (hpb ▸ hBmin)

/-! ## Karger's theorem -/

/-- Every outcome of `s` contractions of a contraction of `W₀` from `t + s ≥ 2` supervertices is a
contraction of `W₀` to `t` supervertices. -/
theorem isContractionOf_of_mem_support_contractTimes {n t : ℕ} (ht : 1 ≤ t)
    {W₀ : Fin n → Fin n → ℕ} (s : ℕ) {W : Fin (t + s) → Fin (t + s) → ℕ}
    {part : Fin n → Fin (t + s)} (hC : IsContractionOf W₀ part W) {x : Unit × Graph}
    (hx : x ∈ (spec.toRandomized.withCoins.run (contractTimes s) ⟨t + s, W⟩).support) :
    ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
      x.2 = ⟨t, W'⟩ ∧ IsContractionOf W₀ part' W' := by
  induction s with
  | zero =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
    exact ⟨W, part, rfl, hC⟩
  | succ s ih =>
    change x ∈ (spec.toRandomized.withCoins.run (contractStep >>= fun _ => contractTimes s)
      ⟨t + s + 1, W⟩).support at hx
    by_cases hS : totalDoubledWeight W = 0
    · rw [run_contractStep_bind_of_eq_zero (m := t + s) _ W hS] at hx
      have h0 : (0 : Fin (t + s + 1)) ≠ Fin.last (t + s) := by
        rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        omega
      exact ih (isContractionOf_contract hC h0) hx
    · rw [run_contractStep_bind (m := t + s) _ W hS, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      obtain ⟨u, v, hsamp⟩ := exists_isSampledPair W (show (r : ℕ) < totalDoubledWeight W by
        have := r.isLt
        omega)
      rw [sampledPair_eq hsamp, contractGraph_fin] at hx
      exact ih (isContractionOf_contract hC (isSampledPair_ne hC.multigraph hsamp)) hx

/-- Running `karger` from `n` supervertices contracts `n - 2` times, then answers half the total
weight. -/
private theorem run_karger {n : ℕ} (W : Fin n → Fin n → ℕ) :
    spec.toRandomized.withCoins.run karger ⟨n, W⟩ =
      (spec.toRandomized.withCoins.run (contractTimes (n - 2)) ⟨n, W⟩).bind fun x =>
        PMF.pure (totalDoubledWeight x.2.weight / 2, x.2) := by
  rw [karger, StateTransitionSpec.run_withCoins_query_bind]
  dsimp only [StateTransitionSpec.stepFn, step]
  rw [RandomizedSpec.run_bind]
  exact congrArg _ (funext fun ⟨_, G⟩ =>
    StateTransitionSpec.run_withCoins_query_bind (D := spec) Op.total (fun S => pure (S / 2)) G)

/-- **Karger's theorem** [Karger1993]. On a connected multigraph with `n ≥ 2` vertices, `karger`
answers the minimum cut weight with probability at least `2 / (n (n - 1))`. -/
theorem two_div_le_toOuterMeasure_karger {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) (hmin : 0 < minCut W₀) :
    (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
      (spec.toRandomized.withCoins.run karger ⟨n, W₀⟩).toOuterMeasure {x | x.1 = minCut W₀} := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 + s := ⟨n - 2, by omega⟩
  obtain ⟨C, hC, hCmin⟩ := exists_minCut_achiever (by rw [Fintype.card_fin]; omega) W₀
  have hid : pullbackCut id C = C := by
    ext x
    simp [mem_pullbackCut]
  have hsurv := survives_contractTimes le_rfl hmin s (isContractionOf_id hW₀) hC
    (by rw [hid, hCmin])
  rw [hid] at hsurv
  rw [run_karger, Nat.add_sub_cancel_left, show (2 : ℝ≥0∞) / ((2 + s) * (2 + s - 1) : ℕ) =
    ((2 * (2 - 1) : ℕ) : ℝ≥0∞) / ((2 + s) * (2 + s - 1) : ℕ) * 1 by norm_num]
  refine Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal _ _ _ _ hsurv
    fun x _ ⟨W', part', B', hx, hC', hpb⟩ => ?_
  have hB' : IsNonTrivialCut B' := isNonTrivialCut_of_pullbackCut part' (hpb ▸ hC)
  have hcut : W' 0 1 = minCut W₀ := by
    rw [← cutWeight_fin_two hC'.multigraph hB', ← cutWeight_pullbackCut hC', hpb, hCmin]
  rw [hx, PMF.toOuterMeasure_pure_apply, ite_eq_left]
  change totalDoubledWeight W' / 2 = minCut W₀
  rw [totalDoubledWeight_fin_two hC'.multigraph, ← hcut]
  omega

/-- The law of the answer of one run of `karger` on `G`. -/
noncomputable def answerLaw (G : Graph) : PMF ℕ :=
  (spec.toRandomized.withCoins.run karger G).map Prod.fst

/-- The answer of `karger` is half the total weight of the graph that `n - 2` contractions leave. -/
theorem answerLaw_eq {n : ℕ} (W : Fin n → Fin n → ℕ) :
    answerLaw ⟨n, W⟩ = ((spec.toRandomized.withCoins.run (contractTimes (n - 2)) ⟨n, W⟩).map
      Prod.snd).map fun G => totalDoubledWeight G.weight / 2 := by
  rw [answerLaw, run_karger, PMF.map_comp, PMF.map_bind]
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- Every answer of `karger` on a multigraph with `n ≥ 2` vertices is the weight of a non-trivial
cut. -/
theorem exists_cut_of_mem_support_answerLaw {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) {v : ℕ} (hv : v ∈ (answerLaw ⟨n, W₀⟩).support) :
    ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ v = cutWeight W₀ C := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 + s := ⟨n - 2, by omega⟩
  rw [answerLaw_eq, PMF.map_comp, PMF.mem_support_map_iff, Nat.add_sub_cancel_left] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨W', part', hx', hC'⟩ :=
    isContractionOf_of_mem_support_contractTimes (t := 2) (by norm_num) s
      (isContractionOf_id hW₀) hx
  obtain ⟨hnt, hcw, -⟩ := two_vertex_contraction_output hC'
  refine ⟨_, hnt, ?_⟩
  change totalDoubledWeight x.2.weight / 2 = _
  rw [hx']
  change totalDoubledWeight W' / 2 = _
  rw [totalDoubledWeight_fin_two hC'.multigraph, ← hcw]
  omega

/-- **One-sided error.** Every answer of `karger` on a multigraph with `n ≥ 2` vertices is the
weight of a non-trivial cut, so it is never below the minimum cut weight. -/
theorem minCut_le_of_mem_support_karger {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) {x : ℕ × Graph}
    (hx : x ∈ (spec.toRandomized.withCoins.run karger ⟨n, W₀⟩).support) : minCut W₀ ≤ x.1 := by
  obtain ⟨C, hC, hx⟩ := exists_cut_of_mem_support_answerLaw hn hW₀
    ((PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩)
  exact hx ▸ minCut_le_cutWeight W₀ hC

/-! ## Amplification -/

/-- One more run of a trial, keeping the least answer `b` so far. The trial is an oracle whose one
call `()` answers one run of `karger`. -/
def minStep (b : ℕ) : OracleComp (fun _ : Unit => ℕ) ℕ := do
  let v ← OracleComp.query ()
  pure (min v b)

/-- **Amplification** [Karger1993]: make `R` runs of a trial and answer the least answer, or `0`
when `R = 0`. Answering each call by an independent run of `karger` on `G`, with
`OracleComp.evalWith (fun _ => answerLaw G)`, gives the law of `R` independent runs. -/
def minRuns : ℕ → OracleComp (fun _ : Unit => ℕ) ℕ
  | 0 => pure 0
  | R + 1 => do
    let v ← OracleComp.query ()
    OracleComp.iterate R minStep v

/-- After the least answer `b` of earlier runs, `R` more runs answer at most `b`: either `b` or the
answer of one of them. -/
theorem mem_support_iterate_minStep {μ : PMF ℕ} {R b v : ℕ}
    (hv : v ∈ (OracleComp.evalWith (fun _ => μ) (OracleComp.iterate R minStep b)).support) :
    v ≤ b ∧ (v = b ∨ v ∈ μ.support) := by
  rw [OracleComp.support_evalWith] at hv
  refine OracleComp.iterate_invariant (fun _ v => v ≤ b ∧ (v = b ∨ v ∈ μ.support))
    ⟨le_rfl, .inl rfl⟩ (fun _ c _ ⟨hcb, hc⟩ next hnext => ?_) v hv
  obtain ⟨u, hu, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
  obtain rfl := OracleComp.eq_of_mem_supportWith_pure hnext
  rw [OracleComp.supportWith_query] at hu
  refine ⟨(min_le_right u c).trans hcb, ?_⟩
  rcases min_choice u c with h | h <;> rw [h]
  · exact .inr hu
  · exact hc

/-- With `R ≥ 1` runs, every answer of `minRuns R` is the answer of one of the runs. -/
theorem mem_support_minRuns {μ : PMF ℕ} {R v : ℕ} (hR : R ≠ 0)
    (hv : v ∈ (OracleComp.evalWith (fun _ => μ) (minRuns R)).support) : v ∈ μ.support := by
  obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hR
  rw [minRuns, OracleComp.evalWith_bind, OracleComp.evalWith_query, PMF.mem_support_bind_iff] at hv
  obtain ⟨u, hu, hv⟩ := hv
  obtain ⟨-, rfl | hv⟩ := mem_support_iterate_minStep hv
  exacts [hu, hv]

/-- **Amplification.** If every answer of a run is at least `m` and a run misses `m` with
probability at most `q`, then `R` independent runs all miss it, so `minRuns R` misses it, with
probability at most `q ^ R`. -/
theorem minRuns_ne_le {μ : PMF ℕ} {m : ℕ} {q : ℝ≥0∞} (hge : ∀ v ∈ μ.support, m ≤ v)
    (hmiss : μ.toOuterMeasure {v | v ≠ m} ≤ q) (R : ℕ) :
    (OracleComp.evalWith (fun _ => μ) (minRuns R)).toOuterMeasure {v | v ≠ m} ≤ q ^ R := by
  have hstep (b : ℕ) :
      OracleComp.evalWith (fun _ => μ) (minStep b) = μ.map fun v => min v b := by
    simp only [minStep, OracleComp.evalWith_bind, OracleComp.evalWith_query,
      OracleComp.evalWith_pure]
    exact PMF.bind_pure_comp _ _
  -- Once a run hits `m`, the least answer stays there.
  have hstay (R : ℕ) :
      (OracleComp.evalWith (fun _ => μ) (OracleComp.iterate R minStep m)).toOuterMeasure
        {v | v ≠ m} = 0 := by
    refine (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
      (Set.disjoint_left.mpr fun v hv hne => hne ?_)
    obtain ⟨hle, rfl | hv⟩ := mem_support_iterate_minStep hv
    · rfl
    · exact le_antisymm hle (hge v hv)
  -- After a least answer of at least `m`, each further run misses independently.
  have hfrom (R : ℕ) : ∀ b, m ≤ b →
      (OracleComp.evalWith (fun _ => μ) (OracleComp.iterate R minStep b)).toOuterMeasure
        {v | v ≠ m} ≤ q ^ R := by
    induction R with
    | zero => exact fun _ _ => (Probability.PMF.toOuterMeasure_le_one _ _).trans (by rw [pow_zero])
    | succ R ih =>
      intro b hb
      rw [OracleComp.iterate_succ_bind, OracleComp.evalWith_bind, pow_succ']
      refine Probability.PMF.toOuterMeasure_bind_le_mul_ennreal _ _ {c | c ≠ m} _ ?_
        (fun c hc _ => ih c ?_) fun c _ hc => by rw [not_not.mp hc]; exact hstay R
      · rw [hstep, PMF.toOuterMeasure_map_apply]
        refine (PMF.toOuterMeasure_mono _ ?_).trans hmiss
        rintro v ⟨hv, -⟩ rfl
        exact hv (min_eq_left hb)
      · rw [hstep, PMF.mem_support_map_iff] at hc
        obtain ⟨v, hv, rfl⟩ := hc
        exact le_min (hge v hv) hb
  cases R with
  | zero => exact (Probability.PMF.toOuterMeasure_le_one _ _).trans (by rw [pow_zero])
  | succ R =>
    rw [minRuns, OracleComp.evalWith_bind, OracleComp.evalWith_query, pow_succ']
    exact Probability.PMF.toOuterMeasure_bind_le_mul_ennreal _ _ {v | v ≠ m} _ hmiss
      (fun v hv _ => hfrom R v (hge v hv)) fun v _ hv => by rw [not_not.mp hv]; exact hstay R

/-- **Amplification of Karger's algorithm** [Karger1993]. On a connected multigraph with `n ≥ 2`
vertices, `R` independent runs of `karger` all miss the minimum cut weight, so `minRuns R` misses
it, with probability at most `(1 - 2 / (n (n - 1))) ^ R`. -/
theorem minRuns_ne_minCut_le {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) (hmin : 0 < minCut W₀) (R : ℕ) :
    (OracleComp.evalWith (fun _ => answerLaw ⟨n, W₀⟩) (minRuns R)).toOuterMeasure
        {v | v ≠ minCut W₀} ≤ (1 - 2 / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ R := by
  refine minRuns_ne_le (fun v hv => ?_) (Probability.PMF.toOuterMeasure_compl_le_one_sub _
    {v | v = minCut W₀} ?_) R
  · obtain ⟨C, hC, rfl⟩ := exists_cut_of_mem_support_answerLaw hn hW₀ hv
    exact minCut_le_cutWeight W₀ hC
  · rw [answerLaw, PMF.toOuterMeasure_map_apply]
    exact two_div_le_toOuterMeasure_karger hn hW₀ hmin

/-! ## Calls -/

/-- One contraction makes at most one coin call and four calls of the structure. -/
theorem isCostBounded_contractStep {cost : ℕ ⊕ Op → ℕ} {a b : ℕ}
    (hcoin : ∀ n, cost (.inl n) ≤ a) (hop : ∀ o, cost (.inr o) ≤ b) :
    OracleComp.IsCostBounded cost contractStep (a + 4 * b) := by
  have hq (o : Op) {m : ℕ} (hm : b ≤ m) :
      OracleComp.IsCostBounded cost (call o) m :=
    (OracleComp.IsCostBounded.query _).mono ((hop o).trans hm)
  have h₁ := hop .size
  have h₂ := hop .total
  refine OracleComp.IsCostBounded.liftBind_iff.mpr ⟨by omega, fun k => ?_⟩
  refine OracleComp.IsCostBounded.liftBind_iff.mpr ⟨by omega, fun S => ?_⟩
  change OracleComp.IsCostBounded cost (if S = 0 then _ else _) _
  split_ifs
  · exact hq _ (by omega)
  · have h₃ := hcoin (S - 1)
    refine OracleComp.IsCostBounded.liftBind_iff.mpr ⟨by omega, fun r => ?_⟩
    have h₄ := hop (.pairAt r)
    exact OracleComp.IsCostBounded.liftBind_iff.mpr ⟨by omega, fun _ => hq _ (by omega)⟩

/-- `s` contractions make at most `s` coin calls and `4 s` calls of the structure. -/
theorem isCostBounded_contractTimes {cost : ℕ ⊕ Op → ℕ} {a b : ℕ}
    (hcoin : ∀ n, cost (.inl n) ≤ a) (hop : ∀ o, cost (.inr o) ≤ b) (s : ℕ) :
    OracleComp.IsCostBounded cost (contractTimes s) (s * (a + 4 * b)) := by
  induction s with
  | zero => exact .pure _ _
  | succ s ih =>
    exact ((isCostBounded_contractStep hcoin hop).bind fun _ => ih).mono
      (le_of_eq (by ring))

/-! ## Admissibility -/

/-- Every call of `s` contractions of a multigraph on `t + s ≥ 2` supervertices is admissible. -/
theorem demonicValid_contractTimes {t : ℕ} (ht : 1 ≤ t) (s : ℕ)
    {W : Fin (t + s) → Fin (t + s) → ℕ} (hW : IsMultigraph W) :
    spec.toRandomized.withCoins.toSpec.DemonicValid ⟨t + s, W⟩ (contractTimes s) := by
  induction s with
  | zero => exact .pure _ _
  | succ s ih =>
    change spec.toRandomized.withCoins.toSpec.DemonicValid ⟨t + s + 1, W⟩
      (contractStep >>= fun _ => contractTimes s)
    simp only [contractStep, bind_assoc]
    refine StateTransitionSpec.demonicValid_withCoins_query_bind trivial
      (StateTransitionSpec.demonicValid_withCoins_query_bind trivial ?_)
    dsimp only [StateTransitionSpec.stepFn, step]
    by_cases hS : totalDoubledWeight W = 0
    · simp only [hS, ite_true]
      refine StateTransitionSpec.demonicValid_withCoins_query_bind
        (show 0 < t + s + 1 ∧ t + s + 1 - 1 < t + s + 1 ∧ 0 ≠ t + s + 1 - 1 by omega) ?_
      dsimp only [StateTransitionSpec.stepFn, step]
      rw [show t + s + 1 - 1 = ((Fin.last (t + s) : Fin (t + s + 1)) : ℕ) from rfl,
        show (0 : ℕ) = ((0 : Fin (t + s + 1)) : ℕ) from rfl, contractGraph_fin]
      exact ih (isMultigraph_contractMatrix hW _ _)
    · simp only [hS, ite_false, bind_assoc]
      refine RandomizedSpec.demonicValid_sample_bind fun r => ?_
      have hr : (r : ℕ) < totalDoubledWeight W := by
        have := r.isLt
        omega
      obtain ⟨u, v, hsamp⟩ := exists_isSampledPair W hr
      refine StateTransitionSpec.demonicValid_withCoins_query_bind hr ?_
      dsimp only [StateTransitionSpec.stepFn, step]
      rw [sampledPair_eq hsamp]
      refine StateTransitionSpec.demonicValid_withCoins_query_bind
        ⟨u.isLt, v.isLt, Fin.val_ne_of_ne (isSampledPair_ne hW hsamp)⟩ ?_
      dsimp only [StateTransitionSpec.stepFn, step]
      rw [contractGraph_fin]
      exact ih (isMultigraph_contractMatrix hW u v)

/-- Every call of `karger` on a multigraph with `n ≥ 2` vertices is admissible. -/
theorem demonicValid_karger {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) :
    spec.toRandomized.withCoins.toSpec.DemonicValid ⟨n, W₀⟩ karger := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 + s := ⟨n - 2, by omega⟩
  refine StateTransitionSpec.demonicValid_withCoins_query_bind trivial ?_
  dsimp only [StateTransitionSpec.stepFn, step]
  rw [Nat.add_sub_cancel_left]
  refine StateTransitionSpec.DemonicValid.bind (demonicValid_contractTimes (by omega) s hW₀)
    fun _ _ _ _ => StateTransitionSpec.demonicValid_withCoins_query_bind trivial (.pure _ _)

end Cslib.Algorithms.Lean.Karger
