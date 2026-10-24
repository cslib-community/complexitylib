/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.CapacityCircuit
public import Complexity.Foundations.Data.Code.Hadamard
import Mathlib.Algebra.BigOperators.Fin

/-!
# Pending-bias state simulation and input-summary lower bounds for threshold circuits

A weighted threshold program of size `g` has a layered finite-state representation across any gate
cut `k`. After the first `k` gates have been evaluated to a Boolean prefix `u : Fin k → Bool`, their
entire effect on the remaining `g - k` gates is captured by the *pending-bias vector*
`pendingBias p k u : Fin (g - k) → ℝ` collecting the internal weighted sums contributed by the
prefix to each future gate. The layered evolution `pendingBiasTrace` computes these states
recursively by evaluating each gate from its direct input sum and the first coordinate of the
current pending-bias vector, then shifting the state and adding the new gate's outgoing internal
weights (Theorem 6.1).

Bounding the syntactic state space `pendingBiasStates p k` yields finite-state width bounds under
bounded fan-in (`2 ^ k`), bounded integer internal weights on a row basis
(`∏ i ∈ rows, (1 + ∑ j, |w i j|)` and `(1 + k * W) ^ rows.card`), or column-constant internal
weights (`k + 1`).

On the input side, the complete gate valuation is determined by the direct input summary
`inputSummary p x`. Whenever a threshold program computes a two-party function `f : X → Y → Bool`,
any summary map on `X` that determines `inputSummary` for every `y : Y` must take at least as many
values as there are distinct rows of `f` (Proposition 9.1), forcing `(1 + |ι| * W) ^ r ≥ 2 ^ |ι|`
for rank-`r` integer summaries of the Hadamard inner-product code. Under phased input access across
cut `k` (gates `< k` reading only `X`, gates `≥ k` reading only `Y`, and readout depending only on
gates `≥ k`), the pending-bias state at cut `k` is a deterministic one-way message from `X` to `Y`,
forcing `(pendingBiasStates p k).card` to be at least the number of distinct rows of `f`.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.gateThreshold`: the threshold of a program gate.
* `Cslib.Circuits.Boolean.WeightedThreshold.pendingBias`: the pending internal bias vector at cut
  `k` from a Boolean prefix `u : Fin k → Bool`.
* `Cslib.Circuits.Boolean.WeightedThreshold.pendingBiasTrace`: the layered pending-bias state
  evolution on input `x`.
* `Cslib.Circuits.Boolean.WeightedThreshold.pendingBiasStates`: the syntactic set of pending-bias
  states at cut `k`.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputSummary`: the direct input-weighted sum vector of
  a program on input `x`.
* `Cslib.Circuits.Boolean.WeightedThreshold.intSummary`: the integer linear summary `u ↦ R u` of a
  Boolean input `u : ι → Bool`.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.pendingBiasTrace_eq_pendingBias`,
  `Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_decide_pendingBiasTrace`: Theorem 6.1, exact
  pending-bias state simulation.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_two_pow`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_prod_intWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_pow_intWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_add_one_of_row_const`:
  Section 6.1 state-space bounds.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_rows_le_card_summaries`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_card_summaries_of_hadamardCode`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_pow_intSummary_of_hadamardCode`:
  Proposition 9.1 input-summary and rank-precision lower bounds.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_rows_le_card_pendingBiasStates_of_phased`,
`Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_card_pendingBiasStates_of_phased_hadamardCode`:
  Section 9 phased-access cut lower bounds.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Sections 6 and 9]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset BitString

variable {n g : ℕ}

/-! ### Helper lemmas for finite-image and integer-box cardinality bounds -/

private theorem card_image_le_of_factorsThrough {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq γ] (f : α → γ) (g : α → β) (hfg : ∀ x y, g x = g y → f x = f y) :
    (univ.image f).card ≤ Fintype.card β := by
  rw [← Fintype.card_coe]
  refine Fintype.card_le_of_injective (fun c : univ.image f => g (mem_image.mp c.2).choose) ?_
  intro c₁ c₂ h
  ext
  rw [← (mem_image.mp c₁.2).choose_spec.2, ← (mem_image.mp c₂.2).choose_spec.2]
  exact hfg _ _ h

private theorem card_image_le_card_image_of_factorsThrough {α β γ : Type*} [Fintype α]
    [DecidableEq β] [DecidableEq γ] (f : α → γ) (g : α → β)
    (hfg : ∀ x y, g x = g y → f x = f y) :
    (univ.image f).card ≤ (univ.image g).card := by
  rw [← Fintype.card_coe (univ.image f), ← Fintype.card_coe (univ.image g)]
  refine Fintype.card_le_of_injective
    (fun c : univ.image f =>
      ⟨g (mem_image.mp c.2).choose, mem_image_of_mem g (mem_univ _)⟩) ?_
  intro c₁ c₂ h
  ext
  rw [← (mem_image.mp c₁.2).choose_spec.2, ← (mem_image.mp c₂.2).choose_spec.2]
  exact hfg _ _ (Subtype.mk.inj h)

private def shiftedIntTerm (z : ℤ) (b : Bool) : ℕ :=
  if 0 ≤ z then z.natAbs * b.toNat else z.natAbs * (1 - b.toNat)

private theorem shiftedIntTerm_le_natAbs (z : ℤ) (b : Bool) :
    shiftedIntTerm z b ≤ z.natAbs := by
  unfold shiftedIntTerm
  cases b <;> split_ifs <;> simp

private theorem coe_shiftedIntTerm (z : ℤ) (b : Bool) :
    (shiftedIntTerm z b : ℤ) = z * b.toNat + if 0 ≤ z then 0 else -z := by
  unfold shiftedIntTerm
  cases b <;> split_ifs <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_mul] <;> omega

private def shiftedIntSum {ι : Type*} [Fintype ι] (w : ι → ℤ) (u : ι → Bool) :
    Fin (1 + ∑ j : ι, (w j).natAbs) :=
  ⟨∑ j : ι, shiftedIntTerm (w j) (u j), by
    have hle : (∑ j : ι, shiftedIntTerm (w j) (u j)) ≤ ∑ j : ι, (w j).natAbs :=
      sum_le_sum fun j _ => shiftedIntTerm_le_natAbs (w j) (u j)
    omega⟩

private theorem sum_int_eq_of_shiftedIntSum_eq {ι : Type*} [Fintype ι] (w : ι → ℤ)
    {u v : ι → Bool} (h : shiftedIntSum w u = shiftedIntSum w v) :
    (∑ j : ι, w j * (u j).toNat) = ∑ j : ι, w j * (v j).toNat := by
  have hval : (∑ j : ι, (shiftedIntTerm (w j) (u j) : ℤ)) =
      ∑ j : ι, (shiftedIntTerm (w j) (v j) : ℤ) := by
    exact_mod_cast congrArg Fin.val h
  simp only [coe_shiftedIntTerm, sum_add_distrib] at hval
  linarith

/-! ### Section 6: Pending-bias state simulation and state-set bounds -/

/-- The threshold of a gate in a weighted threshold program. -/
def gateThreshold (p : Program signature n g) (gate : Fin g) : ℝ :=
  (p.lines gate).op.threshold

/-- At cut `k`, the pending internal bias accumulated at future gate `k + i` from the first
`k` gate outputs `u : Fin k → Bool`. -/
def pendingBias (p : Program signature n g) (k : ℕ) (u : Fin k → Bool)
    (i : Fin (g - k)) : ℝ :=
  have := i.isLt
  ∑ j : Fin k, gateWeight p ⟨k + i.val, by omega⟩ ⟨j.val, by omega⟩ * (u j).toNat

/-- At cut `0`, the pending internal bias is identically zero. -/
@[simp]
theorem pendingBias_zero (p : Program signature n g) (u : Fin 0 → Bool) (i : Fin (g - 0)) :
    pendingBias p 0 u i = 0 := by
  simp [pendingBias]

/-- Stepping from cut `k` to cut `k + 1` shifts the remaining-gate index by one and adds the new
gate's internal-weight contribution. -/
theorem pendingBias_succ (p : Program signature n g) (k : ℕ) (u : Fin (k + 1) → Bool)
    (i : Fin (g - (k + 1))) :
    have := i.isLt
    pendingBias p (k + 1) u i =
      pendingBias p k (fun j => u j.castSucc) ⟨i.val + 1, by omega⟩ +
        gateWeight p ⟨k + 1 + i.val, by omega⟩ ⟨k, by omega⟩ * (u (Fin.last k)).toNat := by
  have := i.isLt
  unfold pendingBias
  rw [Fin.sum_univ_castSucc]
  congr 1
  apply sum_congr rfl
  intro j _
  have hgate : (⟨k + 1 + i.val, by omega⟩ : Fin g) = ⟨k + (i.val + 1), by omega⟩ := by
    ext
    dsimp
    omega
  rw [hgate]
  rfl

/-- The output of `gate` is determined by its direct input-weighted sum and the first coordinate of
the pending-bias vector at cut `gate.val`. -/
theorem eval_eq_decide_pendingBias (p : Program signature n g) (x : Fin n → Bool) (gate : Fin g) :
    p.eval interpretation x gate = decide (gateThreshold p gate ≤
      (∑ a : Fin n, inputWeight p gate a * (x a).toNat) +
        pendingBias p gate.val
          (fun j : Fin gate.val => p.eval interpretation x ⟨j.val, by omega⟩)
          ⟨0, by omega⟩) := by
  have hfilter : (∑ j : Fin g, gateWeight p gate j * (p.eval interpretation x j).toNat) =
      ∑ j ∈ univ.filter (· < gate), gateWeight p gate j * (p.eval interpretation x j).toNat := by
    symm
    apply sum_subset (filter_subset _ _)
    intro j _ hj
    have hle : gate ≤ j := le_of_not_gt fun hlt => hj (mem_filter.mpr ⟨mem_univ _, hlt⟩)
    rw [gateWeight_eq_zero_of_le p gate j hle, zero_mul]
  have hbij :
      pendingBias p gate.val
        (fun j : Fin gate.val => p.eval interpretation x ⟨j.val, by omega⟩)
        ⟨0, by omega⟩ =
      ∑ j ∈ univ.filter (· < gate), gateWeight p gate j * (p.eval interpretation x j).toNat := by
    rw [pendingBias]
    refine sum_bij (fun (j : Fin gate.val) _ => (⟨j.val, lt_trans j.isLt gate.isLt⟩ : Fin g))
      ?_ ?_ ?_ ?_
    · intro j _
      exact mem_filter.mpr ⟨mem_univ _, j.isLt⟩
    · intro j₁ _ j₂ _ h
      exact Fin.ext (by simpa only [Fin.mk.injEq] using h)
    · intro b hb
      exact ⟨⟨b.val, (mem_filter.mp hb).2⟩, mem_univ _, Fin.ext rfl⟩
    · intro j _
      have hgate : (⟨gate.val + 0, by omega⟩ : Fin g) = gate :=
        Fin.ext (Nat.add_zero gate.val)
      rw [hgate]
  rw [eval_gate_eq, gateThreshold, hfilter, hbij]

/-- The layered pending-bias state evolution along the gates of `p` on input `x`. -/
noncomputable def pendingBiasTrace (p : Program signature n g) (x : Fin n → Bool) :
    (k : ℕ) → Fin (g - k) → ℝ
  | 0, _ => 0
  | k + 1, i =>
    have := i.isLt
    have hk : k < g := by omega
    pendingBiasTrace p x k ⟨i.val + 1, by omega⟩ +
      gateWeight p ⟨k + 1 + i.val, by omega⟩ ⟨k, hk⟩ *
        (decide (gateThreshold p ⟨k, hk⟩ ≤
          (∑ a : Fin n, inputWeight p ⟨k, hk⟩ a * (x a).toNat) +
            pendingBiasTrace p x k ⟨0, by omega⟩)).toNat

/-- **Theorem 6.1 (Pending-bias state simulation).** At every layer `k`, the recursively updated
state `pendingBiasTrace p x k` equals the syntactic pending-bias vector of the actual gate prefix
evaluated on `x`. -/
theorem pendingBiasTrace_eq_pendingBias (p : Program signature n g) (x : Fin n → Bool) (k : ℕ) :
    pendingBiasTrace p x k =
      pendingBias p k (fun j : Fin k =>
        if hj : j.val < g then p.eval interpretation x ⟨j.val, hj⟩ else false) := by
  induction k with
  | zero =>
    funext i
    simp [pendingBiasTrace]
  | succ k ih =>
    funext i
    have := i.isLt
    have hk : k < g := by omega
    rw [pendingBiasTrace, pendingBias_succ, ih]
    congr 1
    have hprefix :
        (fun j : Fin k =>
          if hj : j.val < g then p.eval interpretation x ⟨j.val, hj⟩ else false) =
        (fun j : Fin k => p.eval interpretation x ⟨j.val, by omega⟩) := by
      funext j
      have hj : j.val < g := by omega
      simp only [hj, ↓reduceDIte]
    have heval :
        decide (gateThreshold p ⟨k, hk⟩ ≤
          (∑ a : Fin n, inputWeight p ⟨k, hk⟩ a * (x a).toNat) +
            pendingBias p k
              (fun j : Fin k =>
                if hj : j.val < g then p.eval interpretation x ⟨j.val, hj⟩ else false)
              ⟨0, by omega⟩) =
        p.eval interpretation x ⟨k, hk⟩ := by
      rw [hprefix, ← eval_eq_decide_pendingBias p x ⟨k, hk⟩]
    rw [heval]
    simp only [Fin.val_last, hk, ↓reduceDIte]

/-- **Theorem 6.1 (Pending-bias query rule).** Each gate's evaluation is a single linear threshold
query on `x` shifted by the first coordinate of the recursive pending-bias state. -/
theorem eval_eq_decide_pendingBiasTrace (p : Program signature n g) (x : Fin n → Bool)
    (gate : Fin g) :
    p.eval interpretation x gate = decide (gateThreshold p gate ≤
      (∑ a : Fin n, inputWeight p gate a * (x a).toNat) +
        pendingBiasTrace p x gate.val ⟨0, by omega⟩) := by
  rw [eval_eq_decide_pendingBias, pendingBiasTrace_eq_pendingBias]
  congr 4
  funext j
  have hj : j.val < g := by omega
  simp only [hj, ↓reduceDIte]

/-- The syntactic set of pending-bias states at cut `k`, ranging over all Boolean prefixes
`u : Fin k → Bool`. -/
noncomputable def pendingBiasStates (p : Program signature n g) (k : ℕ) :
    Finset (Fin (g - k) → ℝ) :=
  open scoped Classical in
  univ.image (pendingBias p k)

/-- Every Boolean prefix produces a state in `pendingBiasStates p k`. -/
theorem pendingBias_mem_pendingBiasStates (p : Program signature n g) (k : ℕ)
    (u : Fin k → Bool) :
    pendingBias p k u ∈ pendingBiasStates p k := by
  classical
  exact mem_image_of_mem _ (mem_univ u)

/-- The reachable state `pendingBiasTrace p x k` belongs to `pendingBiasStates p k`. -/
theorem pendingBiasTrace_mem_pendingBiasStates (p : Program signature n g) (x : Fin n → Bool)
    (k : ℕ) :
    pendingBiasTrace p x k ∈ pendingBiasStates p k := by
  rw [pendingBiasTrace_eq_pendingBias]
  exact pendingBias_mem_pendingBiasStates p k _

/-- At cut `k`, there are at most `2 ^ k` pending-bias states. -/
theorem card_pendingBiasStates_le_two_pow (p : Program signature n g) (k : ℕ) :
    (pendingBiasStates p k).card ≤ 2 ^ k := by
  classical
  simpa [pendingBiasStates] using card_image_le (f := pendingBias p k) (s := univ)

/-- **Section 6.1 (Integer-weight box bound for pending-bias states).** If a subset `rows` of
remaining gates determines the entire pending-bias vector at cut `k`, and the internal weights into
`rows` from the first `k` gates are integers `w i j`, then the number of pending-bias states is at
most `∏ i ∈ rows, (1 + ∑ j : Fin k, (w i j).natAbs)`. -/
theorem card_pendingBiasStates_le_prod_intWeight (p : Program signature n g) (k : ℕ)
    (rows : Finset (Fin (g - k)))
    (hrows : ∀ u v : Fin k → Bool,
      (∀ i ∈ rows, pendingBias p k u i = pendingBias p k v i) →
        pendingBias p k u = pendingBias p k v)
    (w : Fin (g - k) → Fin k → ℤ)
    (hw : ∀ i ∈ rows, ∀ j : Fin k,
      gateWeight p ⟨k + i.val, by omega⟩ ⟨j.val, by have := i.isLt; omega⟩ = w i j) :
    (pendingBiasStates p k).card ≤ ∏ i ∈ rows, (1 + ∑ j : Fin k, (w i j).natAbs) := by
  classical
  have hle := card_image_le_of_factorsThrough (pendingBias p k)
    (fun (u : Fin k → Bool) (i : rows) => shiftedIntSum (w i.val) u) ?_
  · simp only [Fintype.card_pi, Fintype.card_fin] at hle
    rwa [← prod_attach rows (fun i => 1 + ∑ j : Fin k, (w i j).natAbs)]
  · intro u v huv
    apply hrows u v
    intro i hi
    have hrow : ∀ x : Fin k → Bool,
        pendingBias p k x i = (∑ j : Fin k, w i j * (x j).toNat : ℤ) := by
      intro x
      unfold pendingBias
      push_cast
      apply sum_congr rfl
      intro j _
      rw [hw i hi j]
    rw [hrow u, hrow v]
    exact_mod_cast sum_int_eq_of_shiftedIntSum_eq (w i) (congrFun huv ⟨i, hi⟩)

/-- **Section 6.1, equation (9) (Rank-precision bound for pending-bias states).** Under the
hypotheses of `card_pendingBiasStates_le_prod_intWeight`, if every selected integer internal weight
has magnitude at most `W`, then `(pendingBiasStates p k).card ≤ (1 + k * W) ^ rows.card`. -/
theorem card_pendingBiasStates_le_pow_intWeight (p : Program signature n g) (k W : ℕ)
    (rows : Finset (Fin (g - k)))
    (hrows : ∀ u v : Fin k → Bool,
      (∀ i ∈ rows, pendingBias p k u i = pendingBias p k v i) →
        pendingBias p k u = pendingBias p k v)
    (w : Fin (g - k) → Fin k → ℤ)
    (hw : ∀ i ∈ rows, ∀ j : Fin k,
      gateWeight p ⟨k + i.val, by omega⟩ ⟨j.val, by have := i.isLt; omega⟩ = w i j)
    (hW : ∀ i ∈ rows, ∀ j : Fin k, (w i j).natAbs ≤ W) :
    (pendingBiasStates p k).card ≤ (1 + k * W) ^ rows.card := by
  refine (card_pendingBiasStates_le_prod_intWeight p k rows hrows w hw).trans ?_
  calc
    (∏ i ∈ rows, (1 + ∑ j : Fin k, (w i j).natAbs)) ≤ ∏ _i ∈ rows, (1 + k * W) := by
      apply prod_le_prod
      intro i hi
      have hsum : (∑ j : Fin k, (w i j).natAbs) ≤ k * W := by
        simpa using sum_le_card_nsmul univ (fun j : Fin k => (w i j).natAbs) W
          (fun j _ => hW i hi j)
      omega
    _ = (1 + k * W) ^ rows.card := by simp

/-- **Section 6.1 (Column-constant internal weights).** If every future gate `k + i` assigns a
single weight `β i` to all `k` earlier gates, the pending-bias state depends only on the Hamming
weight of the prefix and has at most `k + 1` values. -/
theorem card_pendingBiasStates_le_add_one_of_row_const (p : Program signature n g) (k : ℕ)
    (β : Fin (g - k) → ℝ)
    (hβ : ∀ (i : Fin (g - k)) (j : Fin k),
      gateWeight p ⟨k + i.val, by omega⟩ ⟨j.val, by have := i.isLt; omega⟩ = β i) :
    (pendingBiasStates p k).card ≤ k + 1 := by
  classical
  have hweight : ∀ u : Fin k → Bool, (∑ j : Fin k, (u j).toNat) < k + 1 := by
    intro u
    have hle : (∑ j : Fin k, (u j).toNat) ≤ k * 1 := by
      simpa using sum_le_card_nsmul univ (fun j : Fin k => (u j).toNat) 1
        (fun j _ => Bool.toNat_le (u j))
    omega
  have hle := card_image_le_of_factorsThrough (pendingBias p k)
    (fun u : Fin k → Bool => (⟨∑ j : Fin k, (u j).toNat, hweight u⟩ : Fin (k + 1))) ?_
  · simpa [pendingBiasStates] using hle
  · intro u v huv
    have hsum : (∑ j : Fin k, (u j).toNat) = ∑ j : Fin k, (v j).toNat :=
      congrArg Fin.val huv
    funext i
    have hrow : ∀ x : Fin k → Bool,
        pendingBias p k x i = β i * (∑ j : Fin k, (x j).toNat : ℕ) := by
      intro x
      unfold pendingBias
      simp only [hβ i, ← mul_sum, Nat.cast_sum]
    rw [hrow u, hrow v, hsum]

/-! ### Section 9: Input summaries and phased-access cut lower bounds -/

/-- The direct input-weighted sum at each gate of `p` on input `x`. -/
def inputSummary (p : Program signature n g) (x : Fin n → Bool) (gate : Fin g) : ℝ :=
  ∑ a : Fin n, inputWeight p gate a * (x a).toNat

/-- Agreement of direct input summaries on all gates below `b` forces agreement of gate evaluations
below `b`. -/
theorem eval_eq_of_inputSummary_eq_lt (p : Program signature n g) {x y : Fin n → Bool} (b : ℕ)
    (h : ∀ gate : Fin g, gate.val < b → inputSummary p x gate = inputSummary p y gate) :
    ∀ gate : Fin g, gate.val < b →
      p.eval interpretation x gate = p.eval interpretation y gate := by
  induction b with
  | zero =>
    intro gate hgate
    omega
  | succ b ih =>
    intro gate hgate
    rw [eval_gate_eq p x gate, eval_gate_eq p y gate]
    have hin : (∑ i, inputWeight p gate i * (x i).toNat) =
        ∑ i, inputWeight p gate i * (y i).toNat := h gate hgate
    rw [hin]
    congr 3
    apply sum_congr rfl
    intro prior _
    by_cases hprior : prior < gate
    · rw [ih (fun j hj => h j (by omega)) prior (by omega)]
    · rw [gateWeight_eq_zero_of_le p gate prior (le_of_not_gt hprior), zero_mul, zero_mul]

/-- Equal direct input summaries produce identical complete gate valuations. -/
theorem eval_eq_of_inputSummary_eq (p : Program signature n g) {x y : Fin n → Bool}
    (h : inputSummary p x = inputSummary p y) :
    p.eval interpretation x = p.eval interpretation y :=
  funext fun gate =>
    eval_eq_of_inputSummary_eq_lt p g (fun j _ => congrFun h j) gate gate.isLt

/-- If `summary x` determines the direct input summary of `enc x y` for every `y`, then equal
summaries force identical row functions `f x₁ = f x₂`. -/
private theorem f_eq_of_summary_eq {X Y α : Type*} (p : Program signature n g)
    (enc : X → Y → (Fin n → Bool)) (readout : (Fin g → Bool) → Bool) (f : X → Y → Bool)
    (summary : X → α)
    (hcomp : ∀ x y, readout (p.eval interpretation (enc x y)) = f x y)
    (hsum : ∀ x₁ x₂ y, summary x₁ = summary x₂ →
      inputSummary p (enc x₁ y) = inputSummary p (enc x₂ y))
    {x₁ x₂ : X} (h : summary x₁ = summary x₂) :
    f x₁ = f x₂ := by
  funext y
  rw [← hcomp x₁ y, ← hcomp x₂ y, eval_eq_of_inputSummary_eq p (hsum x₁ x₂ y h)]

/-- **Proposition 9.1 (Distinct communication rows force distinct input summaries).** If `f` is
computed by a threshold program `p` via `enc` and `readout`, any summary of the left input `X` that
determines `inputSummary p (enc x y)` for every `y` takes at least as many values as there are
distinct rows of `f`. -/
theorem card_rows_le_card_summaries {X Y α : Type*} [Fintype X] [DecidableEq (Y → Bool)]
    [DecidableEq α] (p : Program signature n g) (enc : X → Y → (Fin n → Bool))
    (readout : (Fin g → Bool) → Bool) (f : X → Y → Bool) (summary : X → α)
    (hcomp : ∀ x y, readout (p.eval interpretation (enc x y)) = f x y)
    (hsum : ∀ x₁ x₂ y, summary x₁ = summary x₂ →
      inputSummary p (enc x₁ y) = inputSummary p (enc x₂ y)) :
    (univ.image f).card ≤ (univ.image summary).card :=
  card_image_le_card_image_of_factorsThrough f summary fun _ _ h =>
    f_eq_of_summary_eq p enc readout f summary hcomp hsum h

/-- **Proposition 9.1 (Hadamard input-summary lower bound).** Any summary of `x : ι → Bool` that
determines the direct input weights of a threshold program computing `hadamardCode` has at least
`2 ^ Fintype.card ι` distinct values. -/
theorem two_pow_le_card_summaries_of_hadamardCode {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (p : Program signature n g)
    (enc : (ι → Bool) → (ι → Bool) → (Fin n → Bool))
    (readout : (Fin g → Bool) → Bool) (summary : (ι → Bool) → α)
    (hcomp : ∀ x y, readout (p.eval interpretation (enc x y)) = hadamardCode x y)
    (hsum : ∀ x₁ x₂ y, summary x₁ = summary x₂ →
      inputSummary p (enc x₁ y) = inputSummary p (enc x₂ y)) :
    2 ^ Fintype.card ι ≤ (univ.image summary).card := by
  classical
  have hcard : (univ.image (hadamardCode (ι := ι))).card = 2 ^ Fintype.card ι := by
    rw [card_image_of_injective _ hadamardCode_injective, card_univ, Fintype.card_fun,
      Fintype.card_bool]
  rw [← hcard]
  exact card_rows_le_card_summaries p enc readout hadamardCode summary hcomp hsum

/-- The integer linear summary `u ↦ R u` of a Boolean input `u : ι → Bool` by an integer matrix
`R : Fin r → ι → ℤ`. -/
def intSummary {ι : Type*} [Fintype ι] {r : ℕ} (R : Fin r → ι → ℤ) (u : ι → Bool) :
    Fin r → ℤ :=
  fun a => ∑ i : ι, R a i * (u i).toNat

/-- Each row `a` of `intSummary R` takes at most `1 + ∑ i, (R a i).natAbs` values on the Boolean
cube. -/
private theorem card_intSummary_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (R : Fin r → ι → ℤ) :
    (univ.image (intSummary R)).card ≤ ∏ a : Fin r, (1 + ∑ i : ι, (R a i).natAbs) := by
  have hle := card_image_le_of_factorsThrough (intSummary R)
    (fun (u : ι → Bool) (a : Fin r) => shiftedIntSum (R a) u) ?_
  · simpa [Fintype.card_pi, Fintype.card_fin] using hle
  · intro u v huv
    funext a
    exact sum_int_eq_of_shiftedIntSum_eq (R a) (congrFun huv a)

/-- If all entries of `R : Fin r → ι → ℤ` have magnitude at most `W`, then `intSummary R` takes at
most `(1 + Fintype.card ι * W) ^ r` values on the Boolean cube. -/
theorem card_intSummary_le_pow {ι : Type*} [Fintype ι] [DecidableEq ι] {r W : ℕ}
    (R : Fin r → ι → ℤ) (hW : ∀ a i, (R a i).natAbs ≤ W) :
    (univ.image (intSummary R)).card ≤ (1 + Fintype.card ι * W) ^ r := by
  refine (card_intSummary_le_prod R).trans ?_
  calc
    (∏ a : Fin r, (1 + ∑ i : ι, (R a i).natAbs)) ≤ ∏ _a : Fin r, (1 + Fintype.card ι * W) := by
      apply prod_le_prod
      intro a _
      have hsum : (∑ i : ι, (R a i).natAbs) ≤ Fintype.card ι * W := by
        simpa using sum_le_card_nsmul univ (fun i : ι => (R a i).natAbs) W fun i _ => hW a i
      omega
    _ = (1 + Fintype.card ι * W) ^ r := by simp

/-- **Proposition 9.1 (Integer summary product bound for inner product).** If an integer matrix
`R : Fin r → ι → ℤ` determines the direct input weights of a threshold program computing
`hadamardCode`, the product of its row ranges is at least `2 ^ Fintype.card ι`. -/
theorem two_pow_le_prod_intSummary_of_hadamardCode {ι : Type*} [Fintype ι] {r : ℕ}
    (p : Program signature n g) (enc : (ι → Bool) → (ι → Bool) → (Fin n → Bool))
    (readout : (Fin g → Bool) → Bool) (R : Fin r → ι → ℤ)
    (hcomp : ∀ x y, readout (p.eval interpretation (enc x y)) = hadamardCode x y)
    (hsum : ∀ x₁ x₂ y, intSummary R x₁ = intSummary R x₂ →
      inputSummary p (enc x₁ y) = inputSummary p (enc x₂ y)) :
    2 ^ Fintype.card ι ≤ ∏ a : Fin r, (1 + ∑ i : ι, (R a i).natAbs) := by
  classical
  exact (two_pow_le_card_summaries_of_hadamardCode p enc readout (intSummary R) hcomp hsum).trans
    (card_intSummary_le_prod R)

/-- **Proposition 9.1, equation (20) (Rank-precision bound for inner product).** If an integer
matrix `R : Fin r → ι → ℤ` with entries bounded in magnitude by `W` determines the direct input
weights of a threshold program computing `hadamardCode`, then
`2 ^ Fintype.card ι ≤ (1 + Fintype.card ι * W) ^ r`. -/
theorem two_pow_le_pow_intSummary_of_hadamardCode {ι : Type*} [Fintype ι] {r W : ℕ}
    (p : Program signature n g) (enc : (ι → Bool) → (ι → Bool) → (Fin n → Bool))
    (readout : (Fin g → Bool) → Bool) (R : Fin r → ι → ℤ)
    (hW : ∀ a i, (R a i).natAbs ≤ W)
    (hcomp : ∀ x y, readout (p.eval interpretation (enc x y)) = hadamardCode x y)
    (hsum : ∀ x₁ x₂ y, intSummary R x₁ = intSummary R x₂ →
      inputSummary p (enc x₁ y) = inputSummary p (enc x₂ y)) :
    2 ^ Fintype.card ι ≤ (1 + Fintype.card ι * W) ^ r := by
  classical
  exact (two_pow_le_card_summaries_of_hadamardCode p enc readout (intSummary R) hcomp hsum).trans
    (card_intSummary_le_pow R hW)

private theorem pendingBiasTrace_add_eq_of_pendingBiasTrace_eq (p : Program signature n g)
    {z₁ z₂ : Fin n → Bool} (k : ℕ)
    (hinit : pendingBiasTrace p z₁ k = pendingBiasTrace p z₂ k)
    (hsuff : ∀ (i : Fin (g - k)),
      inputSummary p z₁ ⟨k + i.val, by omega⟩ = inputSummary p z₂ ⟨k + i.val, by omega⟩) :
    ∀ d : ℕ, pendingBiasTrace p z₁ (k + d) = pendingBiasTrace p z₂ (k + d) := by
  intro d
  induction d with
  | zero => simpa using hinit
  | succ d ih =>
    funext i
    have := i.isLt
    have hkd : k + d < g := by omega
    have hin : inputSummary p z₁ ⟨k + d, hkd⟩ = inputSummary p z₂ ⟨k + d, hkd⟩ :=
      hsuff ⟨d, by omega⟩
    unfold inputSummary at hin
    change pendingBiasTrace p z₁ ((k + d) + 1) i = pendingBiasTrace p z₂ ((k + d) + 1) i
    rw [pendingBiasTrace, pendingBiasTrace, ih, hin]

/-- Under phased input access across cut `k`, the pending-bias state
`pendingBiasTrace p (enc x y₀) k` at a reference right input `y₀` determines the entire row `f x`.
-/
private theorem f_eq_of_pendingBiasTrace_eq_of_phased {X Y : Type*} (p : Program signature n g)
    (enc : X → Y → (Fin n → Bool)) (readout : (Fin g → Bool) → Bool) (f : X → Y → Bool)
    (k : ℕ) (y₀ : Y)
    (hcomp : ∀ x y, readout (p.eval interpretation (enc x y)) = f x y)
    (hpref : ∀ (j : Fin k) (hj : j.val < g) (x : X) (y : Y),
      inputSummary p (enc x y) ⟨j.val, hj⟩ = inputSummary p (enc x y₀) ⟨j.val, hj⟩)
    (hsuff : ∀ (i : Fin (g - k)) (x₁ x₂ : X) (y : Y),
      inputSummary p (enc x₁ y) ⟨k + i.val, by omega⟩ =
        inputSummary p (enc x₂ y) ⟨k + i.val, by omega⟩)
    (hread : ∀ z₁ z₂ : Fin g → Bool,
      (∀ i : Fin (g - k), z₁ ⟨k + i.val, by omega⟩ = z₂ ⟨k + i.val, by omega⟩) →
        readout z₁ = readout z₂)
    {x₁ x₂ : X}
    (htrace : pendingBiasTrace p (enc x₁ y₀) k = pendingBiasTrace p (enc x₂ y₀) k) :
    f x₁ = f x₂ := by
  have htrace_indep : ∀ (x : X) (y : Y),
      pendingBiasTrace p (enc x y) k = pendingBiasTrace p (enc x y₀) k := by
    intro x y
    rw [pendingBiasTrace_eq_pendingBias, pendingBiasTrace_eq_pendingBias]
    congr 1
    funext j
    by_cases hj : j.val < g
    · simp only [hj, ↓reduceDIte]
      exact eval_eq_of_inputSummary_eq_lt p k
        (fun gate hgate => hpref ⟨gate.val, hgate⟩ gate.isLt x y) ⟨j.val, hj⟩ j.isLt
    · simp only [hj, ↓reduceDIte]
  funext y
  rw [← hcomp x₁ y, ← hcomp x₂ y]
  apply hread
  intro i
  have hinit : pendingBiasTrace p (enc x₁ y) k = pendingBiasTrace p (enc x₂ y) k := by
    rw [htrace_indep x₁ y, htrace_indep x₂ y, htrace]
  have hstep :=
    pendingBiasTrace_add_eq_of_pendingBiasTrace_eq p k hinit
      (fun j => hsuff j x₁ x₂ y) i.val
  have hin : (∑ a : Fin n, inputWeight p ⟨k + i.val, by omega⟩ a * (enc x₁ y a).toNat) =
      ∑ a : Fin n, inputWeight p ⟨k + i.val, by omega⟩ a * (enc x₂ y a).toNat :=
    hsuff i x₁ x₂ y
  rw [eval_eq_decide_pendingBiasTrace, eval_eq_decide_pendingBiasTrace, hin]
  simp only [hstep]

/-- **Section 9 (Phased-access pending-bias cut bound).** If gates before cut `k` read only the
left input `X`, gates from `k` onward read only the right input `Y`, and the readout depends only
on gates from `k` onward, then `(pendingBiasStates p k).card` is at least the number of distinct
rows of `f`. -/
theorem card_rows_le_card_pendingBiasStates_of_phased {X Y : Type*} [Fintype X]
    [DecidableEq (Y → Bool)] (p : Program signature n g)
    (enc : X → Y → (Fin n → Bool)) (readout : (Fin g → Bool) → Bool) (f : X → Y → Bool)
    (k : ℕ) (y₀ : Y)
    (hcomp : ∀ x y, readout (p.eval interpretation (enc x y)) = f x y)
    (hpref : ∀ (j : Fin k) (hj : j.val < g) (x : X) (y : Y),
      inputSummary p (enc x y) ⟨j.val, hj⟩ = inputSummary p (enc x y₀) ⟨j.val, hj⟩)
    (hsuff : ∀ (i : Fin (g - k)) (x₁ x₂ : X) (y : Y),
      inputSummary p (enc x₁ y) ⟨k + i.val, by omega⟩ =
        inputSummary p (enc x₂ y) ⟨k + i.val, by omega⟩)
    (hread : ∀ z₁ z₂ : Fin g → Bool,
      (∀ i : Fin (g - k), z₁ ⟨k + i.val, by omega⟩ = z₂ ⟨k + i.val, by omega⟩) →
        readout z₁ = readout z₂) :
    (univ.image f).card ≤ (pendingBiasStates p k).card := by
  classical
  have hle : (univ.image f).card ≤
      (univ.image (fun x : X => pendingBiasTrace p (enc x y₀) k)).card :=
    card_image_le_card_image_of_factorsThrough f (fun x => pendingBiasTrace p (enc x y₀) k)
      fun _ _ h =>
        f_eq_of_pendingBiasTrace_eq_of_phased p enc readout f k y₀ hcomp hpref hsuff hread h
  refine hle.trans (card_le_card ?_)
  intro s hs
  obtain ⟨x, _, rfl⟩ := mem_image.mp hs
  exact pendingBiasTrace_mem_pendingBiasStates p (enc x y₀) k

/-- **Section 9 (Phased-access pending-bias bound for inner product).** Under phased input access
across cut `k`, any threshold program computing `hadamardCode` has at least `2 ^ Fintype.card ι`
pending-bias states at cut `k`. -/
theorem two_pow_le_card_pendingBiasStates_of_phased_hadamardCode {ι : Type*} [Fintype ι]
    (p : Program signature n g) (enc : (ι → Bool) → (ι → Bool) → (Fin n → Bool))
    (readout : (Fin g → Bool) → Bool) (k : ℕ)
    (hcomp : ∀ x y, readout (p.eval interpretation (enc x y)) = hadamardCode x y)
    (hpref : ∀ (j : Fin k) (hj : j.val < g) (x y : ι → Bool),
      inputSummary p (enc x y) ⟨j.val, hj⟩ =
        inputSummary p (enc x (fun _ => false)) ⟨j.val, hj⟩)
    (hsuff : ∀ (i : Fin (g - k)) (x₁ x₂ y : ι → Bool),
      inputSummary p (enc x₁ y) ⟨k + i.val, by omega⟩ =
        inputSummary p (enc x₂ y) ⟨k + i.val, by omega⟩)
    (hread : ∀ z₁ z₂ : Fin g → Bool,
      (∀ i : Fin (g - k), z₁ ⟨k + i.val, by omega⟩ = z₂ ⟨k + i.val, by omega⟩) →
        readout z₁ = readout z₂) :
    2 ^ Fintype.card ι ≤ (pendingBiasStates p k).card := by
  classical
  have hcard : (univ.image (hadamardCode (ι := ι))).card = 2 ^ Fintype.card ι := by
    rw [card_image_of_injective _ hadamardCode_injective, card_univ, Fintype.card_fun,
      Fintype.card_bool]
  rw [← hcard]
  exact card_rows_le_card_pendingBiasStates_of_phased p enc readout hadamardCode k
    (fun _ => false) hcomp hpref hsuff hread

end Cslib.Circuits.Boolean.WeightedThreshold
