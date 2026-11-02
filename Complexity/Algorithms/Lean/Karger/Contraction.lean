/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Karger.Graph
public import Complexity.DataStructure.StateTransition.Randomized

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
weight with probability at least `2 / (n (n - 1))` (`two_div_le_toOuterMeasure_karger`), and never
less than it (`minCut_le_of_mem_support_karger`). Every call it makes is admissible
(`demonicValid_karger`). The combinatorics and the one-step bound are `Karger.Graph`'s
(`isContractionOf_contract`, `pullbackCut_contractCut`, `step_survival_prob_ge`,
`telescope_survival_step`), used unchanged, and the composition of the stages is
`Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal`.

The word-RAM implementation proves the same bound on machine states, interleaved with register
steps (`Cslib.Algorithms.WordRAM.Karger.contractDownTo_spec`). Here no register, address or
instruction count appears. An implementation of `spec` over the memory oracle is a separate,
deterministic hop, and `Refinement.toRandomized` with `RandomizedRefinement.withCoins` carries the
law of the client through it.

## Main definitions

* `Graph`, `Op`, `step`, `valid`, `spec`: the contraction structure.
* `sampledPair`, `contractGraph`: the pair sampled at an offset, and contraction.
* `contractStep`, `contractTimes`, `karger`: the algorithm as a client with coins.
* `Survives`: a cut of the input survives in a contracted graph.

## Main results

* `survives_contractTimes`: the survival bound.
* `two_div_le_toOuterMeasure_karger`: Karger's success probability.
* `isContractionOf_of_mem_support_contractTimes`, `minCut_le_of_mem_support_karger`: every
  outcome is a contraction, so the answer is never below the minimum cut weight.
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
  | s + 1 => contractStep >>= fun _ => contractTimes s

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
private theorem run_contractStep_bind {α : Type} (p : ProbOracleComp Op.Result α) {m : ℕ}
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
private theorem run_contractStep_bind_of_eq_zero {α : Type} (p : ProbOracleComp Op.Result α)
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

/-- Running `karger` from `n = 2 + s` supervertices contracts `s` times, then answers half the
total weight. -/
private theorem run_karger {s : ℕ} (W : Fin (2 + s) → Fin (2 + s) → ℕ) :
    spec.toRandomized.withCoins.run karger ⟨2 + s, W⟩ =
      (spec.toRandomized.withCoins.run (contractTimes s) ⟨2 + s, W⟩).bind fun x =>
        PMF.pure (totalDoubledWeight x.2.weight / 2, x.2) := by
  rw [karger, StateTransitionSpec.run_withCoins_query_bind]
  dsimp only [StateTransitionSpec.stepFn, step]
  rw [Nat.add_sub_cancel_left, RandomizedSpec.run_bind]
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
  rw [run_karger, show (2 : ℝ≥0∞) / ((2 + s) * (2 + s - 1) : ℕ) =
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

/-- **One-sided error.** Every answer of `karger` on a multigraph with `n ≥ 2` vertices is the
weight of a non-trivial cut, so it is never below the minimum cut weight. -/
theorem minCut_le_of_mem_support_karger {n : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) {x : ℕ × Graph}
    (hx : x ∈ (spec.toRandomized.withCoins.run karger ⟨n, W₀⟩).support) : minCut W₀ ≤ x.1 := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 + s := ⟨n - 2, by omega⟩
  rw [run_karger, PMF.mem_support_bind_iff] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨W', part', hy', hC'⟩ :=
    isContractionOf_of_mem_support_contractTimes (t := 2) (by norm_num) s
      (isContractionOf_id hW₀) hy
  obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
  obtain ⟨-, hcw, hle⟩ := two_vertex_contraction_output hC'
  change minCut W₀ ≤ totalDoubledWeight y.2.weight / 2
  rw [hy']
  change minCut W₀ ≤ totalDoubledWeight W' / 2
  rw [totalDoubledWeight_fin_two hC'.multigraph]
  omega

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
