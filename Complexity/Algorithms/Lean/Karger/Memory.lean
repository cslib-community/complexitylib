/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Karger.Memory.Contract
public import Complexity.DataStructure.Memory.Frame
public import Complexity.Foundations.Analysis.Asymptotics.CostBound

/-!
# The contraction structure over memory

The contraction structure `Karger.spec` is implemented over the memory oracle `Memory.spec w` by
the programs of `Karger.Memory.Layout` (`size`, `total`, `pairAt`) and `Karger.Memory.Contract`
(`contract`), on the layout of a `Layout`. This file assembles them into a refinement.

* `refinement`: a `Refinement Karger.spec (Memory.spec w)` with invariant `Inv` and abstraction
  `abs`.
* `amortized`: each operation on a graph of `k` supervertices costs at most `opCharge`, which is
  one memory unit for `size` and `total`, `2 k + 1` for `pairAt` and `7 k + 7` for `contract`.
  So `amortized_capacity` bounds every operation by `7 C + 7` at capacity `C`.
* `framed`: the same refinement as a `Memory.Framed`, whose footprint is the layout's region, so
  it joins products with other structures in one memory.

Each obligation comes from one weakest-precondition lemma per operation (`wp_methods`), through
`StateTransitionSpec.wp_iff`. Nothing here mentions a register or an instruction.

**Karger's algorithm over memory** (`kargerProg`) is the client `karger` linked through the
refinement with its coins passed through (`hop`, which is `refinement.toRandomized.withCoins`).
Every law proved on the specification transfers through `RandomizedRefinement.run_link`
(`map_run_kargerProg`): the success probability `2 / (n (n - 1))` and the one-sided error. The
costs transfer through `Refinement.Amortized.toRandomized` and
`RandomizedRefinement.ExpectedAmortized.withCoins`: the expected memory cost, counting a unit per
coin, is at most `(n - 2) (1 + 4 (7 C + 7)) + 2 (7 C + 7)` at capacity `C`
(`expectedCost_kargerProg_le`), which is `O(n²)` when the layout is sized to the input
(`exists_expectedCost_kargerProg_isBigO`).

## Main definitions

* `methods`, `opCharge`: the operations as memory programs, and their charges.
* `refinement`, `framed`: the implementation as a refinement, and as a framed one.
* `hop`, `kargerProg`: the distributional hop, and Karger's algorithm over memory.

## Main results

* `wp_methods`: each operation realizes the specified step, preserves the invariant, costs at
  most `opCharge`, and changes no cell outside the layout.
* `amortized`, `amortized_capacity`: the cost certificates.
* `map_run_kargerProg`: the law of Karger's algorithm over memory, read through the abstraction,
  is its law on the specification.
* `two_div_le_toOuterMeasure_kargerProg`, `minCut_le_of_mem_support_kargerProg`: Karger's
  theorem and the one-sided error over memory.
* `expectedCost_karger_le`: the expected charge of `karger` on the specification.
* `expectedCost_kargerProg_le`, `expectedCoins_kargerProg_le`: the expected memory cost and the
  expected number of coins over memory.
* `exists_expectedCost_kargerProg_isBigO`: the expected memory cost is `O(n²)`.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Karger.Memory

open Cslib.WordRAM Cslib.WeightedCut Cslib.DataStructure Cslib.DataStructure.Memory
  Cslib.DataStructure.StateTransitionSpec

variable (L : Layout) (w : ℕ)

/-- The operations of the contraction structure as memory programs. -/
def methods : Methods spec (Memory.spec w)
  | .size => size L
  | .total => total L
  | .pairAt r => pairAt L r
  | .contract u v => contract L u v

/-- The memory charge of each operation on a graph of `k` supervertices: one unit for the size
and the total, `2 k + 1` for the sampling query, and `7 k + 7` for a contraction. -/
def opCharge (G : Graph) : Op → ℕ
  | .size => 1
  | .total => 1
  | .pairAt _ => 2 * G.size + 1
  | .contract _ _ => 7 * G.size + 7

variable {L w}

/-- **Every operation over memory.** From a state satisfying the invariant, each admissible
operation answers and steps as the specification, preserves the invariant, costs at most
`opCharge`, keeps the frontier and changes no cell outside the layout. -/
theorem wp_methods {s : Memory.State} (hs : Inv L w s) (o : Op) (hv : spec.valid (abs L s) o) :
    (Memory.spec w).wp charge (methods L w o)
      (fun a s' t => spec.stepFn (abs L s) o = (abs L s', a) ∧ Inv L w s' ∧
        t ≤ opCharge (abs L s) o ∧ s'.frontier = s.frontier ∧
        ∀ b ∉ L.footprint, s'.mem b = s.mem b) s := by
  have hlim := hs.allocated
  cases o with
  | size =>
    exact (wp_lift _ _ _).mpr
      ⟨hs.lt_frontier L.size_mem_footprint, rfl, hs, le_rfl, rfl, fun _ _ => rfl⟩
  | total =>
    refine (wp_lift _ _ _).mpr
      ⟨hs.lt_frontier L.total_mem_footprint, ?_, hs, le_rfl, rfl, fun _ _ => rfl⟩
    change (abs L s, totalDoubledWeight (abs L s).weight) = (abs L s, s.mem L.total.base)
    rw [hs.total_eq]
  | pairAt r =>
    refine wp_mono ?_ (wp_pairAt hs hv)
    rintro a s' t ⟨rfl, rfl, ht⟩
    exact ⟨rfl, hs, ht, rfl, fun _ _ => rfl⟩
  | contract u v =>
    refine wp_mono ?_ (wp_contract hs hv)
    rintro a s' t ⟨hf, hfr, habs, hs', ht⟩
    exact ⟨by rw [habs]; rfl, hs', ht, hf, hfr⟩

variable (L w)

/-- **The contraction structure over memory.** -/
noncomputable def refinement : Refinement spec (Memory.spec w) :=
  Refinement.ofFn (methods L w) (Inv L w) (abs L)
    (fun o hs hv => ((wp_iff _ _ _).mp (wp_methods hs o hv)).1)
    (fun o hs hv => by
      obtain ⟨-, hstep, hs', -⟩ := (wp_iff _ _ _).mp (wp_methods hs o hv)
      exact ⟨hstep, hs'⟩)

@[simp] theorem refinement_methods : (refinement L w).methods = methods L w := rfl

@[simp] theorem refinement_inv : (refinement L w).inv = Inv L w := rfl

@[simp] theorem refinement_abs : (refinement L w).abs = abs L := rfl

/-- **Cost.** Each operation costs at most `opCharge` memory units, with no potential. -/
theorem amortized : (refinement L w).Amortized charge opCharge fun _ => 0 :=
  Refinement.Amortized.ofFn fun o hs hv => by
    obtain ⟨-, -, -, ht, -⟩ := (wp_iff _ _ _).mp (wp_methods hs o hv)
    simpa using ht

/-- At most `capacity` supervertices, every operation costs at most `7 capacity + 7` memory
units. -/
theorem amortized_capacity :
    (refinement L w).Amortized charge (fun _ _ => 7 * L.capacity + 7) fun _ => 0 := by
  refine ⟨fun {e} o {a e' tr} hs hv hrun => ((amortized L w).step o hs hv hrun).trans ?_⟩
  have hk : ((refinement L w).abs e).size ≤ L.capacity := hs.size_le
  cases o <;> simp only [opCharge] <;> omega

/-- **The framed implementation.** The refinement, with the layout's region as its footprint. -/
noncomputable def framed : Memory.Framed spec w :=
  .ofStatic (refinement L w) L.footprint (fun hs ha => Inv.lt_frontier hs ha)
    (fun hs h hf => ⟨hs.congr h hf, abs_congr hs h⟩)
    (fun o hs hv b _ hb => by
      obtain ⟨-, -, -, -, -, hfr⟩ := (wp_iff _ _ _).mp (wp_methods hs o hv)
      exact hfr b hb)

@[simp] theorem framed_toRefinement : (framed L w).toRefinement = refinement L w := rfl

/-- The framed implementation has the same costs. -/
theorem framed_amortized : (framed L w).Amortized charge opCharge fun _ => 0 :=
  amortized L w

/-! ## Karger's algorithm over memory -/

/-- The distributional hop: the memory implementation, with coins passed through. -/
noncomputable abbrev hop : RandomizedRefinement spec.toRandomized.withCoins
    (Memory.spec w).toRandomized.withCoins :=
  (refinement L w).toRandomized.withCoins

/-- **Karger's algorithm over memory**: `karger`, with every call of the contraction structure
replaced by its memory program. -/
noncomputable def kargerProg : ProbOracleComp Memory.Op.Result ℕ := link (hop L w).methods karger

variable {L w}

/-- **The law transfers.** From a memory state satisfying the invariant, the law of Karger's
algorithm over memory, read through the abstraction, is the law of `karger` on the specification,
provided `karger` is admissible there. -/
theorem map_run_kargerProg {e : Memory.State} (he : Inv L w e)
    (hv : spec.toRandomized.withCoins.toSpec.DemonicValid (abs L e) karger) :
    ((Memory.spec w).toRandomized.withCoins.run (kargerProg L w) e).map
        (fun (a, e') => (a, abs L e')) =
      spec.toRandomized.withCoins.run karger (abs L e) :=
  (hop L w).run_link karger he hv

/-- **Karger's theorem over memory.** From a memory state holding a connected multigraph on
`n ≥ 2` vertices, Karger's algorithm over memory answers the minimum cut weight with probability
at least `2 / (n (n - 1))`. -/
theorem two_div_le_toOuterMeasure_kargerProg {e : Memory.State} (he : Inv L w e) {n : ℕ}
    {W₀ : Fin n → Fin n → ℕ} (habs : abs L e = ⟨n, W₀⟩) (hn : 2 ≤ n) (hW₀ : IsMultigraph W₀)
    (hmin : 0 < minCut W₀) :
    (2 : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal) ≤
      ((Memory.spec w).toRandomized.withCoins.run (kargerProg L w) e).toOuterMeasure
        {x | x.1 = minCut W₀} := by
  have h := two_div_le_toOuterMeasure_karger hn hW₀ hmin
  rw [← habs, ← map_run_kargerProg he (habs ▸ demonicValid_karger hn hW₀),
    PMF.toOuterMeasure_map_apply] at h
  exact h

/-- **One-sided error over memory.** Every answer of Karger's algorithm over memory, from a
memory state holding a multigraph on `n ≥ 2` vertices, is at least the minimum cut weight. -/
theorem minCut_le_of_mem_support_kargerProg {e : Memory.State} (he : Inv L w e) {n : ℕ}
    {W₀ : Fin n → Fin n → ℕ} (habs : abs L e = ⟨n, W₀⟩) (hn : 2 ≤ n) (hW₀ : IsMultigraph W₀)
    {x : ℕ × Memory.State}
    (hx : x ∈ ((Memory.spec w).toRandomized.withCoins.run (kargerProg L w) e).support) :
    minCut W₀ ≤ x.1 := by
  have hmem : (x.1, abs L x.2) ∈ (spec.toRandomized.withCoins.run karger ⟨n, W₀⟩).support := by
    rw [← habs, ← map_run_kargerProg he (habs ▸ demonicValid_karger hn hW₀)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩
  exact minCut_le_of_mem_support_karger hn hW₀ hmem

/-! ## Cost -/

/-- Over a deterministic specification with coins, a call charges its cost, then continues with
its answer from the next state. -/
theorem expectedCost_withCoins_query_bind {D : StateTransitionSpec.{0, 0, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f] {β : Type}
    (coin : ℕ → ℕ) (c : D.State → D.Op → ℕ) (o : D.Op)
    (k : D.Result o → ProbOracleComp D.Result β) (s : D.State) :
    D.toRandomized.withCoins.expectedCost (D.toRandomized.coinCharge coin c)
        (ProbOracleComp.query o >>= k) s =
      c s o + D.toRandomized.withCoins.expectedCost (D.toRandomized.coinCharge coin c)
        (k (D.stepFn s o).2) (D.stepFn s o).1 := by
  change D.toRandomized.withCoins.expectedCost _ (.liftBind (Sum.inr o) k) s = _
  rw [RandomizedSpec.expectedCost_liftBind]
  change (c s o : ENNReal) + ∑' x, PMF.pure ((D.stepFn s o).2, (D.stepFn s o).1) x * _ = _
  rw [tsum_eq_single ((D.stepFn s o).2, (D.stepFn s o).1) fun x hx => by
    simp [PMF.pure_apply, hx], PMF.pure_apply_self, one_mul]

/-- **Expected calls of `karger` on the specification.** From a graph on `n` vertices, at one unit
per coin and `K` per call of the structure, `karger` costs at most `(n - 2) (1 + 4 K) + 2 K` in
expectation. -/
theorem expectedCost_karger_le {n : ℕ} (W : Fin n → Fin n → ℕ) (K : ℕ) :
    spec.toRandomized.withCoins.expectedCost
        (spec.toRandomized.coinCharge (fun _ => 1) fun _ _ => K) karger ⟨n, W⟩ ≤
      ((n - 2) * (1 + 4 * K) + 2 * K : ℕ) := by
  have hc : spec.toRandomized.coinCharge (fun _ => 1) (fun _ _ => K) =
      fun _ o => Sum.elim (fun _ => 1) (fun _ => K) o := by
    funext _ o
    cases o <;> rfl
  have h₁ := RandomizedSpec.expectedCost_le_of_isCostBounded (D := spec.toRandomized.withCoins)
    (isCostBounded_contractTimes (cost := Sum.elim (fun _ => 1) (fun _ => K)) (a := 1) (b := K)
      (fun _ => le_rfl) (fun _ => le_rfl) (n - 2)) ⟨n, W⟩
  rw [← hc] at h₁
  rw [karger, expectedCost_withCoins_query_bind, RandomizedSpec.expectedCost_bind]
  dsimp only [StateTransitionSpec.stepFn, step]
  have h₂ : ∀ x : Unit × Graph, spec.toRandomized.withCoins.expectedCost
      (spec.toRandomized.coinCharge (fun _ => 1) fun _ _ => K)
        (call .total >>= fun S => pure (S / 2)) x.2 = K := fun x => by
    rw [expectedCost_withCoins_query_bind, RandomizedSpec.expectedCost_pure, add_zero]
  simp only [h₂, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc (K : ENNReal) + (_ + K) ≤ K + ((((n - 2) * (1 + 4 * K) : ℕ) : ENNReal) + K) := by gcongr
    _ = _ := by push_cast; ring

/-- **Expected memory cost of Karger's algorithm.** From a memory state holding a multigraph on
`n ≥ 2` vertices at capacity `C`, Karger's algorithm over memory costs at most
`(n - 2) (1 + 4 (7 C + 7)) + 2 (7 C + 7)` memory units in expectation, counting one unit per
coin. -/
theorem expectedCost_kargerProg_le {e : Memory.State} (he : Inv L w e) {n : ℕ}
    {W₀ : Fin n → Fin n → ℕ} (habs : abs L e = ⟨n, W₀⟩) (hn : 2 ≤ n) (hW₀ : IsMultigraph W₀) :
    (Memory.spec w).toRandomized.withCoins.expectedCost
        ((Memory.spec w).toRandomized.coinCharge (fun _ => 1) charge) (kargerProg L w) e ≤
      ((n - 2) * (1 + 4 * (7 * L.capacity + 7)) + 2 * (7 * L.capacity + 7) : ℕ) := by
  have hv : spec.toRandomized.withCoins.toSpec.DemonicValid (abs L e) karger :=
    habs ▸ demonicValid_karger hn hW₀
  have h := ((amortized_capacity L w).toRandomized.withCoins (coin := fun _ => 1)).client karger
    he hv
  simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero] at h
  change _ ≤ spec.toRandomized.withCoins.expectedCost _ karger (abs L e) at h
  rw [habs] at h
  exact h.trans (expectedCost_karger_le W₀ _)

/-- **Expected coins of Karger's algorithm over memory.** It draws at most `n - 2` coins in
expectation. -/
theorem expectedCoins_kargerProg_le {e : Memory.State} (he : Inv L w e) {n : ℕ}
    {W₀ : Fin n → Fin n → ℕ} (habs : abs L e = ⟨n, W₀⟩) (hn : 2 ≤ n) (hW₀ : IsMultigraph W₀) :
    (Memory.spec w).toRandomized.withCoins.expectedCost
        ((Memory.spec w).toRandomized.coinCharge (fun _ => 1) fun _ _ => 0) (kargerProg L w) e ≤
      (n - 2 : ℕ) := by
  have A : (refinement L w).Amortized (fun _ _ => 0) (fun _ _ => 0) fun _ => 0 :=
    ⟨fun _ _ _ _ => by simp [StateTransitionSpec.totalCostTranscript_const]⟩
  have hv : spec.toRandomized.withCoins.toSpec.DemonicValid (abs L e) karger :=
    habs ▸ demonicValid_karger hn hW₀
  have h := (A.toRandomized.withCoins (coin := fun _ => 1)).client karger he hv
  simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero] at h
  change _ ≤ spec.toRandomized.withCoins.expectedCost _ karger (abs L e) at h
  rw [habs] at h
  refine (h.trans (expectedCost_karger_le W₀ 0)).trans_eq ?_
  simp

/-- **The exported cost.** With the layout sized to the input, the expected memory cost of
Karger's algorithm over memory on `n` vertices is at most `F n` for some `F` that is `O(n²)`. -/
theorem exists_expectedCost_kargerProg_isBigO :
    ∃ F : ℕ → ℕ, CostIsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ 2) id F ∧
      ∀ {L : Layout} {w : ℕ} {e : Memory.State} {n : ℕ} {W₀ : Fin n → Fin n → ℕ},
        Inv L w e → abs L e = ⟨n, W₀⟩ → L.capacity = n → 2 ≤ n → IsMultigraph W₀ →
          (Memory.spec w).toRandomized.withCoins.expectedCost
            ((Memory.spec w).toRandomized.coinCharge (fun _ => 1) charge) (kargerProg L w) e ≤
            (F n : ENNReal) := by
  refine ⟨fun n => n * (1 + 4 * (7 * n + 7)) + 2 * (7 * n + 7), ?_,
    fun {L w e n W₀} he habs hC hn hW₀ => ?_⟩
  · refine CostIsBigO.of_le_nat (F := fun n => n * (1 + 4 * (7 * n + 7)) + 2 * (7 * n + 7))
      (fun a b hab => by dsimp only; gcongr) ?_ fun _ => le_rfl
    refine Asymptotics.IsBigO.of_bound 85 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    push_cast
    nlinarith
  · refine (expectedCost_kargerProg_le he habs hn hW₀).trans ?_
    rw [hC]
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le n 2)) _

end Cslib.Algorithms.Lean.Karger.Memory
