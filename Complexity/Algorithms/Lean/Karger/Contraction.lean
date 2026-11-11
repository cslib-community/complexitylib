/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Karger.Graph
public import Complexity.DataStructure.StateTransition.Randomized
public import Complexity.Foundations.Combinatorics.WeightedCut.Blocks
public import Complexity.Languages.Probabilistic.Iteration
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Probability.PMF.Map

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

All probability is proved here, on the specification. Run laws are derived over `trackedSpec n`, the
same structure that also keeps the block of original vertices merged into each supervertex
(`TrackedGraph`, [Karger and Stein, Section 2][KargerStein1996]). The blocks are bookkeeping:
forgetting them maps every run over `trackedSpec n` to the run of the same client over `spec`
(`map_run_trackedSpec`), so each statement about `spec` is the corresponding statement over the
blocks with the blocks forgotten. Contracting from `t + s` down to `t` supervertices preserves a
fixed minimum cut with probability at least `t (t - 1) / ((t + s) (t + s - 1))`
(`trackedSurvives_contractTimes`, hence `survives_contractTimes`). One run of `karger` over
`trackedSpec n` also outputs a cut, the block of the second of the two supervertices it leaves
(`TrackedGraph.side`, with law `cutLaw W₀`), and answers its weight (`answer_eq_cutWeight_side`,
`answerLaw_eq_map_cutLaw`). A minimum cut that survives down to two supervertices is the output
cut, up to complement, so `karger` outputs a fixed minimum cut with probability at least
`2 / (n (n - 1))` (`two_div_le_cutLaw`). Hence it answers the minimum cut weight with at least that
probability (`two_div_le_toOuterMeasure_karger`), and every answer is the weight of a non-trivial
cut (`exists_cut_of_mem_support_answerLaw`), never less than the minimum
(`minCut_le_of_mem_support_karger`). Every call it makes is admissible (`demonicValid_karger`).
The combinatorics and the one-step bound are `Karger.Graph`'s (`isContractionOf_contract`,
`pullbackCut_contractCut`, `step_survival_prob_ge`, `telescope_survival_step`), used unchanged,
and the composition of the stages is `Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal`. The
bound on the number of minimum cuts is in `Complexity.Algorithms.Lean.Karger.MinCutCount`.

Source map for the output cut ([KargerStein1996], author copy dated 6 August 1996):

* Section 2, the blocks `s(a)` and the output cut `(s(a), s(b))`: `TrackedGraph`,
  `TrackedGraph.side`.
* Lemma 2.1 (a cut is output if and only if no edge crossing it is contracted): the direction
  used, a cut that survives is output, is `two_div_le_cutLaw`'s final step, with
  `TrackedSurvives` for the event that no crossing edge was contracted.
* Theorem 2.2, a particular minimum cut is output with probability at least `C(n, 2)⁻¹`:
  `two_div_le_cutLaw`.

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
* `TrackedGraph`, `contractTracked`, `trackedStep`, `trackedSpec`: the contraction structure with
  blocks.
* `contractStep`, `contractTimes`, `karger`: the algorithm as a client with coins.
* `answerLaw`: the law of the answer of one run of `karger`.
* `TrackedGraph.side`, `cutLaw`: the cut that one run of `karger` outputs, and its law.
* `minStep`, `minRuns`: amplification, as a client of a trial oracle.
* `TrackedSurvives`, `Survives`: a cut of the input survives in a contraction, with and without
  blocks.

## Main results

* `map_run_trackedSpec`: forgetting the blocks maps runs over `trackedSpec n` to runs over `spec`.
* `run_contractStep_bind`, `run_contractStep_bind_of_eq_zero`: the run of one contraction, the
  step that an implementation simulates.
* `trackedSurvives_contractTimes`, `survives_contractTimes`: the survival bound.
* `cutLaw_eq`: the output cut is the block of supervertex `1` after `n - 2` contractions.
* `answer_eq_cutWeight_side`, `answerLaw_eq_map_cutLaw`, `isNonTrivialCut_of_mem_support_cutLaw`:
  the answer is the weight of the output cut, which is non-trivial.
* `two_div_le_cutLaw`: each minimum cut is output with probability at least `2 / (n (n - 1))`.
* `two_div_le_toOuterMeasure_karger`: Karger's success probability.
* `exists_of_mem_support_tracked_contractTimes`, `isContractionOf_of_mem_support_contractTimes`,
  `exists_cut_of_mem_support_answerLaw`, `minCut_le_of_mem_support_karger`: every outcome is a
  contraction, so the answer is the weight of a non-trivial cut, never below the minimum.
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
@[no_expose]
def TrackedGraph.toGraph {n : ℕ} (G : TrackedGraph n) : Graph := ⟨G.size, G.weight⟩

/-- The singleton blocks of the uncontracted graph `W`. -/
@[no_expose]
def TrackedGraph.init {n : ℕ} (W : Fin n → Fin n → ℕ) : TrackedGraph n :=
  ⟨n, W, fun i => pullbackCut id {i}⟩

/-- Contraction with blocks: `contractGraph` on the weights, and `contractBlocks` on the blocks.
Arguments out of range leave the graph unchanged. -/
@[no_expose]
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
@[no_expose]
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

/-- **The blocks are bookkeeping.** Every client with coins draws the same answers and the same
graphs over the structure with blocks as over `spec`: `TrackedGraph.toGraph` represents the state
(`Cslib.ProbOracleComp.run_interpret_map_state`). -/
theorem map_run_trackedSpec {n : ℕ} {α : Type} (p : ProbOracleComp Op.Result α)
    (G : TrackedGraph n) :
    ((trackedSpec n).toRandomized.withCoins.run p G).map (fun x => (x.1, x.2.toGraph)) =
      spec.toRandomized.withCoins.run p G.toGraph :=
  ProbOracleComp.run_interpret_map_state _ _ TrackedGraph.toGraph
    (fun o G => by
      change (PMF.pure ((trackedStep G o).2, (trackedStep G o).1)).map _ =
        PMF.pure ((step G.toGraph o).2, (step G.toGraph o).1)
      rw [PMF.pure_map, ← trackedStep_toGraph G o]) p G

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

/-- One contraction of a graph of positive weight draws a uniform offset below the weight and
contracts the pair sampled there. -/
theorem run_contractStep_bind {α : Type} (p : ProbOracleComp Op.Result α) {m : ℕ}
    (W : Fin (m + 1) → Fin (m + 1) → ℕ) (hS : totalDoubledWeight W ≠ 0) :
    spec.toRandomized.withCoins.run (contractStep >>= fun _ => p) ⟨m + 1, W⟩ =
      (ProbComp.unifOracle (totalDoubledWeight W - 1)).bind fun r =>
        spec.toRandomized.withCoins.run p
          (contractGraph ⟨m + 1, W⟩ (sampledPair W r).1 (sampledPair W r).2) := by
  have h := congrArg (PMF.map fun x => (x.1, x.2.toGraph))
    (run_tracked_contractStep_bind (n := 0) p W (fun _ => ∅) hS)
  rw [map_run_trackedSpec, PMF.map_bind] at h
  refine h.trans (congrArg _ (funext fun r => ?_))
  rw [map_run_trackedSpec, toGraph_contractTracked]
  rfl

/-- One contraction of a weightless graph contracts its first and last supervertices. -/
theorem run_contractStep_bind_of_eq_zero {α : Type} (p : ProbOracleComp Op.Result α)
    {m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ) (hS : totalDoubledWeight W = 0) :
    spec.toRandomized.withCoins.run (contractStep >>= fun _ => p) ⟨m + 1, W⟩ =
      spec.toRandomized.withCoins.run p ⟨m, contractMatrix W 0 (Fin.last m)⟩ := by
  have h := congrArg (PMF.map fun x => (x.1, x.2.toGraph))
    (run_tracked_contractStep_bind_of_eq_zero (n := 0) p W (fun _ => ∅) hS)
  rw [map_run_trackedSpec, map_run_trackedSpec] at h
  exact h

/-! ## Survival of a minimum cut -/

/-- The cut `C` of `W₀` survives in `G`: `G` is a contraction of `W₀` to `t` supervertices along
a map whose fibres are the blocks of `G`, under which `C` is the preimage of a cut. -/
@[no_expose]
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

/-- The cut `C` of `W₀` survives in `G`: `G` is a contraction of `W₀` to `t` supervertices along
some map, under which `C` is the preimage of a cut. -/
def Survives {n : ℕ} (W₀ : Fin n → Fin n → ℕ) (C : Finset (Fin n)) (t : ℕ) (G : Graph) : Prop :=
  ∃ (W : Fin t → Fin t → ℕ) (part : Fin n → Fin t) (B : Finset (Fin t)),
    G = ⟨t, W⟩ ∧ IsContractionOf W₀ part W ∧ pullbackCut part B = C

/-- A cut that survives over the blocks survives in the graph. -/
theorem TrackedSurvives.survives {n : ℕ} {W₀ : Fin n → Fin n → ℕ} {C : Finset (Fin n)} {t : ℕ}
    {G : TrackedGraph n} (h : TrackedSurvives W₀ C t G) : Survives W₀ C t G.toGraph := by
  obtain ⟨W, part, B, rfl, hC, hB⟩ := h
  exact ⟨W, part, B, rfl, hC, hB⟩

/-- **Survival of a minimum cut** [KargerStein1996]. Contracting a contraction of a connected
multigraph `W₀` from `t + s` down to `t ≥ 2` supervertices preserves a fixed minimum cut with
probability at least `t (t - 1) / ((t + s) (t + s - 1))`. This is `trackedSurvives_contractTimes`
with the blocks forgotten. -/
theorem survives_contractTimes {n t : ℕ} (ht : 2 ≤ t) {W₀ : Fin n → Fin n → ℕ}
    (hmin : 0 < minCut W₀) (s : ℕ) {W : Fin (t + s) → Fin (t + s) → ℕ}
    {part : Fin n → Fin (t + s)} (hC : IsContractionOf W₀ part W) {B : Finset (Fin (t + s))}
    (hB : IsNonTrivialCut B) (hBmin : cutWeight W₀ (pullbackCut part B) = minCut W₀) :
    ((t * (t - 1) : ℕ) : ℝ≥0∞) / (((t + s) * (t + s - 1) : ℕ) : ℝ≥0∞) ≤
      (spec.toRandomized.withCoins.run (contractTimes s) ⟨t + s, W⟩).toOuterMeasure
        {x | Survives W₀ (pullbackCut part B) t x.2} := by
  refine (trackedSurvives_contractTimes ht hmin s hC hB hBmin).trans ?_
  rw [show (⟨t + s, W⟩ : Graph) =
      (⟨t + s, W, fun i => pullbackCut part {i}⟩ : TrackedGraph n).toGraph from rfl,
    ← map_run_trackedSpec, PMF.toOuterMeasure_map_apply]
  exact PMF.toOuterMeasure_mono _ fun x hx => hx.1.survives

/-! ## Every outcome is a contraction -/

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

/-- Every outcome of `s` contractions of a contraction of `W₀` from `t + s ≥ 2` supervertices is a
contraction of `W₀` to `t` supervertices. This is `exists_of_mem_support_tracked_contractTimes`
with the blocks forgotten. -/
theorem isContractionOf_of_mem_support_contractTimes {n t : ℕ} (ht : 1 ≤ t)
    {W₀ : Fin n → Fin n → ℕ} (s : ℕ) {W : Fin (t + s) → Fin (t + s) → ℕ}
    {part : Fin n → Fin (t + s)} (hC : IsContractionOf W₀ part W) {x : Unit × Graph}
    (hx : x ∈ (spec.toRandomized.withCoins.run (contractTimes s) ⟨t + s, W⟩).support) :
    ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
      x.2 = ⟨t, W'⟩ ∧ IsContractionOf W₀ part' W' := by
  rw [show (⟨t + s, W⟩ : Graph) =
      (⟨t + s, W, fun i => pullbackCut part {i}⟩ : TrackedGraph n).toGraph from rfl,
    ← map_run_trackedSpec, PMF.mem_support_map_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨W', part', hy', hC'⟩ := exists_of_mem_support_tracked_contractTimes ht s hC hy
  exact ⟨W', part', by rw [hy']; rfl, hC'⟩

/-! ## The output cut -/

/-- The cut that a tracked contraction to two supervertices outputs: the block of supervertex
`1`. -/
@[no_expose]
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

/-- The law of the answer of one run of `karger` on `G`. -/
noncomputable def answerLaw (G : Graph) : PMF ℕ :=
  (spec.toRandomized.withCoins.run karger G).map Prod.fst

/-- The answer of `karger` is half the total weight of the graph that `n - 2` contractions leave. -/
theorem answerLaw_eq {n : ℕ} (W : Fin n → Fin n → ℕ) :
    answerLaw ⟨n, W⟩ = ((spec.toRandomized.withCoins.run (contractTimes (n - 2)) ⟨n, W⟩).map
      Prod.snd).map fun G => totalDoubledWeight G.weight / 2 := by
  rw [answerLaw, show (⟨n, W⟩ : Graph) = (TrackedGraph.init W).toGraph from rfl,
    ← map_run_trackedSpec, ← map_run_trackedSpec, run_karger_tracked, PMF.map_comp, PMF.map_comp,
    PMF.map_comp, PMF.map_bind]
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- The law of the cut that one run of `karger` outputs on `W`: the block of the second of the two
supervertices it leaves. -/
@[no_expose]
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

/-- **Karger's theorem for a fixed cut** [KargerStein1996]. On a connected multigraph on `Fin n`,
`karger` outputs a fixed minimum cut `{C, Cᶜ}` with probability at least
`2 / (n (n - 1)) = 1 / C(n, 2)`. (`C` non-trivial forces `n ≥ 2`.) -/
theorem two_div_le_cutLaw {n : ℕ} {W₀ : Fin n → Fin n → ℕ} (hW₀ : IsMultigraph W₀)
    (hmin : 0 < minCut W₀) {C : Finset (Fin n)} (hC : IsNonTrivialCut C)
    (hCmin : cutWeight W₀ C = minCut W₀) :
    (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
      (cutLaw W₀).toOuterMeasure {C, Finset.univ \ C} := by
  have hn : 2 ≤ n := by
    have := (isNonTrivialCut_iff_card C).mp hC
    rw [Fintype.card_fin] at this
    omega
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

/-! ## Karger's theorem -/

/-- **Karger's theorem** [Karger1993]. On a connected multigraph with `n ≥ 2` vertices, `karger`
answers the minimum cut weight with probability at least `2 / (n (n - 1))`. -/
theorem two_div_le_toOuterMeasure_karger {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) (hmin : 0 < minCut W₀) :
    (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
      (spec.toRandomized.withCoins.run karger ⟨n, W₀⟩).toOuterMeasure {x | x.1 = minCut W₀} := by
  obtain ⟨C, hC, hCmin⟩ := exists_minCut_achiever (by rw [Fintype.card_fin]; omega) W₀
  refine (two_div_le_cutLaw hW₀ hmin hC hCmin).trans ?_
  rw [show (⟨n, W₀⟩ : Graph) = (TrackedGraph.init W₀).toGraph from rfl, ← map_run_trackedSpec,
    PMF.toOuterMeasure_map_apply, cutLaw, PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_mono _ fun x ⟨hx, hsupp⟩ => ?_
  change x.1 = minCut W₀
  rw [(answer_eq_cutWeight_side hn hW₀ hsupp).2]
  rcases hx with hx | hx
  · rw [show x.2.side = C from hx, hCmin]
  · rw [show x.2.side = Finset.univ \ C from hx, cutWeight_compl hW₀, hCmin]

/-- Every answer of `karger` on a multigraph with `n ≥ 2` vertices is the weight of a non-trivial
cut. -/
theorem exists_cut_of_mem_support_answerLaw {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) {v : ℕ} (hv : v ∈ (answerLaw ⟨n, W₀⟩).support) :
    ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ v = cutWeight W₀ C := by
  rw [answerLaw_eq_map_cutLaw hn hW₀, PMF.mem_support_map_iff] at hv
  obtain ⟨C, hC, rfl⟩ := hv
  exact ⟨C, isNonTrivialCut_of_mem_support_cutLaw hn hW₀ hC, rfl⟩

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
