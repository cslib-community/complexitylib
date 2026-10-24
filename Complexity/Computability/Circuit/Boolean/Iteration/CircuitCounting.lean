/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Optimization
public import Complexity.Foundations.Combinatorics.FunctionalGraph.Powers
public import Cslib.Computability.Circuit.Counting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit description counts and hard powers for the native Boolean circuit model

For a finite signature `σ`, `Signature.lineCount σ w` counts the lines that can be formed from `w`
available wires, and `Signature.orderedBudget σ n m G` counts the topologically ordered circuit
descriptions with `n` inputs, `m` designated outputs, and at most `G` internal gates. Because every
function in `Circuit.functionsAtMost I n m G` is computed by some such description, at most
`σ.orderedBudget n m G` functions on `n` inputs and `m` outputs have circuits of size at most `G`
(`Circuit.card_functionsAtMost_le`). Any finite family of functions larger than the ordered-syntax
budget therefore contains a function requiring more than `G` gates
(`Circuit.exists_hard_in_family`).

For the native De Morgan basis `Boolean.signature` (which charges constants, NOT, AND, and OR),
`boolean_lineCount_le` bounds `lineCount w` by `5 * (w + 1) ^ 2`, and `boolean_orderedBudget_le`
and `boolean_orderedBudget_le_pow` bound `orderedBudget n m q`. Combining this with the exact
number `maxTransientDepth g + cyclePeriod g` of distinct powers of a finite map `g`
(`FunctionalGraph.card_range_iterate`) shows that whenever the ordered-syntax budget for `q` gates
is smaller than `maxTransientDepth g + cyclePeriod g`, some power `g^[T]` with
`T < maxTransientDepth g + cyclePeriod g` requires more than `q` gates
(`exists_hard_power_of_budget_lt`, `exists_hard_power`).

## Main definitions

* `Cslib.Circuits.Signature.lineCount`: number of lines over `σ` from `w` available wires.
* `Cslib.Circuits.Signature.orderedBudget`: number of topologically ordered circuits with `n`
  inputs, `m` outputs, and at most `G` gates.
* `Cslib.Circuits.Circuit.functionsAtMost`: functions computed by circuits of size at most `G`.
* `Cslib.Circuits.Boolean.Iteration.lowerBudget`: explicit exponential gate threshold
  `2 ^ k / (1024 * (k + 1))`.

## Main results

* `Cslib.Circuits.Circuit.card_functionsAtMost_le`: at most `σ.orderedBudget n m G` functions have
  circuits of size at most `G`.
* `Cslib.Circuits.Circuit.exists_hard_in_family`: a family larger than `σ.orderedBudget n m G`
  contains a function requiring more than `G` gates.
* `Cslib.Circuits.Boolean.Iteration.boolean_lineCount_le`,
  `Cslib.Circuits.Boolean.Iteration.boolean_orderedBudget_le`,
  `Cslib.Circuits.Boolean.Iteration.boolean_orderedBudget_le_pow`: explicit syntax bounds for the
  native De Morgan basis.
* `Cslib.Circuits.Boolean.Iteration.exists_hard_power_of_budget_lt`,
  `Cslib.Circuits.Boolean.Iteration.exists_hard_power`: existence of a hard power below
  `maxTransientDepth g + cyclePeriod g`.

## References

* Adapted from lean/Proofs/{CircuitCounting,NumberOfPowers}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits

open scoped BigOperators

universe v u

variable {σ : Signature.{v}} [Fintype σ.Op] {U : Type u}

/-- Number of possible lines over `σ` when `w` wires are available. -/
def Signature.lineCount (σ : Signature.{v}) [Fintype σ.Op] (w : ℕ) : ℕ :=
  ∑ op : σ.Op, w ^ σ.Arity op

/-- The number of lines with `n` inputs and `g` prior gates is `σ.lineCount (n + g)`. -/
theorem Line.card_eq_lineCount (n g : ℕ) :
    Nat.card (Line σ n g) = σ.lineCount (n + g) := by
  rw [Line.card, finsum_eq_sum_of_fintype]
  rfl

/-- Number of topologically ordered circuit descriptions with `n` inputs, `m` designated outputs,
and at most `G` internal gates. -/
def Signature.orderedBudget (σ : Signature.{v}) [Fintype σ.Op] (n m G : ℕ) : ℕ :=
  ∑ g ∈ Finset.range (G + 1),
    (∏ j ∈ Finset.range g, σ.lineCount (n + j)) * (n + g) ^ m

/-- Functions from `Fin n → U` to `Fin m → U` computed by circuits with at most `G` gates. -/
noncomputable def Circuit.functionsAtMost (I : Interpretation σ U) (n m G : ℕ) :
    Finset ((Fin n → U) → Fin m → U) :=
  open scoped Classical in
  (Finset.range (G + 1)).biUnion fun g =>
    let := Fintype.ofFinite (Program σ n g × (Fin m → Wire n g))
    Finset.univ.image fun p : Program σ n g × (Fin m → Wire n g) =>
      (⟨p.1, p.2⟩ : Circuit σ n m).eval I

/-- A function belongs to `Circuit.functionsAtMost I n m G` iff it is computed by a circuit of
size at most `G`. -/
theorem Circuit.mem_functionsAtMost_iff {I : Interpretation σ U} {n m G : ℕ}
    {target : (Fin n → U) → Fin m → U} :
    target ∈ Circuit.functionsAtMost I n m G ↔
      ∃ c : Circuit σ n m, c.size ≤ G ∧ c.Computes I target := by
  classical
  simp only [Circuit.functionsAtMost, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and, Nat.lt_succ_iff, Prod.exists]
  constructor
  · rintro ⟨g, hg, p, out, rfl⟩
    exact ⟨⟨p, out⟩, hg, fun _ => rfl⟩
  · rintro ⟨⟨p, out⟩, hs, hc⟩
    exact ⟨_, hs, p, out, funext hc⟩

/-- At most `σ.orderedBudget n m G` functions are computed by circuits of size at most `G`. -/
theorem Circuit.card_functionsAtMost_le (I : Interpretation σ U) {n m G : ℕ} :
    (Circuit.functionsAtMost I n m G).card ≤ σ.orderedBudget n m G := by
  classical
  refine Finset.card_biUnion_le.trans ?_
  unfold Signature.orderedBudget
  apply Finset.sum_le_sum
  intro g _
  let := Fintype.ofFinite (Program σ n g × (Fin m → Wire n g))
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_prod, Program.card,
    Nat.card_fun, Nat.card_eq_fintype_card, Wire.card, Nat.card_fin]
  simp only [Signature.lineCount, finsum_eq_sum_of_fintype, le_rfl]

/-- Any finite family of functions larger than `σ.orderedBudget n m G` contains a function
requiring more than `G` gates. -/
theorem Circuit.exists_hard_in_family (I : Interpretation σ U) {n m G : ℕ}
    (family : Finset ((Fin n → U) → Fin m → U))
    (large : σ.orderedBudget n m G < family.card) :
    ∃ target ∈ family, ∀ c : Circuit σ n m, c.size ≤ G → ¬c.Computes I target := by
  classical
  obtain ⟨target, hmem, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    ((Circuit.card_functionsAtMost_le I).trans_lt large)
  refine ⟨target, hmem, fun c hs hc => hnot ?_⟩
  exact Circuit.mem_functionsAtMost_iff.mpr ⟨c, hs, hc⟩

end Cslib.Circuits

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.FunctionalGraph
open scoped BigOperators

/-- Over the native De Morgan basis, at most `5 * (w + 1) ^ 2` lines can be formed from `w`
available wires. -/
theorem boolean_lineCount_le (w : ℕ) :
    signature.lineCount w ≤ 5 * (w + 1) ^ 2 := by
  unfold Signature.lineCount
  have h (op : Op) : w ^ signature.Arity op ≤ (w + 1) ^ 2 := by
    calc
      _ ≤ (w + 1) ^ signature.Arity op := Nat.pow_le_pow_left (by omega) _
      _ ≤ (w + 1) ^ 2 := Nat.pow_le_pow_right (by omega) (by cases op <;> simp)
  calc
    _ ≤ ∑ _ : Op, (w + 1) ^ 2 := Finset.sum_le_sum fun op _ => h op
    _ = _ := by simp

/-- Constants, arbitrary fanout, and all designated outputs are counted in the De Morgan syntax
budget. -/
theorem boolean_orderedBudget_le (n m q : ℕ) :
    signature.orderedBudget n m q ≤
      (q + 1) * 5 ^ q * (n + q + 1) ^ (2 * q + m) := by
  let W := n + q + 1
  have hW : 1 ≤ W := by dsimp [W]; omega
  have ht (g : ℕ) (hg : g ∈ Finset.range (q + 1)) :
      (∏ j ∈ Finset.range g, signature.lineCount (n + j)) * (n + g) ^ m ≤
        5 ^ q * W ^ (2 * q + m) := by
    have hgq : g ≤ q := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hg
    have hp : (∏ j ∈ Finset.range g, signature.lineCount (n + j)) ≤
        (5 * W ^ 2) ^ g := by
      calc
        _ ≤ ∏ _j ∈ Finset.range g, 5 * W ^ 2 := by
          apply Finset.prod_le_prod
          intro j hj
          have hjq : n + j + 1 ≤ W := by have := Finset.mem_range.mp hj; dsimp [W]; omega
          exact (boolean_lineCount_le _).trans (by gcongr)
        _ = _ := by simp
    calc
      _ ≤ (5 * W ^ 2) ^ g * W ^ m := by gcongr; dsimp [W]; omega
      _ ≤ (5 * W ^ 2) ^ q * W ^ m := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
  unfold Signature.orderedBudget
  calc
    _ ≤ ∑ _g ∈ Finset.range (q + 1), 5 ^ q * W ^ (2 * q + m) := Finset.sum_le_sum ht
    _ = _ := by simp [W, Nat.mul_assoc]

/-- Binary logarithmic bound on the De Morgan syntax budget when the wire budget is at most
`2 ^ h`. -/
theorem boolean_orderedBudget_le_pow (n m q h : ℕ) (hw : n + q + 1 ≤ 2 ^ h) :
    signature.orderedBudget n m q ≤ 2 ^ (3 * q + h * (2 * q + m + 1)) := by
  calc
    _ ≤ (q + 1) * 5 ^ q * (n + q + 1) ^ (2 * q + m) := boolean_orderedBudget_le _ _ _
    _ ≤ 2 ^ h * (2 ^ 3) ^ q * (2 ^ h) ^ (2 * q + m) := by
      gcongr
      · omega
      · decide
    _ = _ := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

/-- For `k ≥ 64`, `128 * (k + 2) ^ 2 ≤ 2 ^ k`. -/
theorem square_le_exponential (k : ℕ) (hk : 64 ≤ k) :
    128 * (k + 2) ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show 2 ^ (k + 1) = 2 ^ k * 2 by rw [Nat.pow_succ]]
    have hsq : (k + 1 + 2) ^ 2 ≤ 2 * (k + 2) ^ 2 := by nlinarith
    nlinarith

/-- Explicit exponential gate threshold `2 ^ k / (1024 * (k + 1))` for `2 k`-bit modular
counters. -/
def lowerBudget (k : ℕ) : ℕ := 2 ^ k / (1024 * (k + 1))

/-- The number of descriptions below `lowerBudget k` has binary logarithm strictly below
`2 ^ k - 1 - k`. -/
theorem lowerBudget_description_exponent (k : ℕ) (hk : 64 ≤ k) :
    let q := lowerBudget k
    3 * q + (k + 2) * (2 * q + (k + k) + 1) + k < 2 ^ k - 1 := by
  dsimp only
  have hq : lowerBudget k * (1024 * (k + 1)) ≤ 2 ^ k := Nat.div_mul_le_self _ _
  have hs := square_le_exponential k hk
  have hpoly : (k + 2) * (k + k + 1) + k + 2 ≤ 4 * (k + 2) ^ 2 := by nlinarith
  have hcoef : (2 * (k + 2) + 3) * 128 ≤ 1024 * (k + 1) := by omega
  have hq' := Nat.mul_le_mul_right (lowerBudget k) hcoef
  have htotal : 128 * (3 * lowerBudget k +
      (k + 2) * (2 * lowerBudget k + (k + k) + 1) + k + 2) ≤ 5 * 2 ^ k := by
    nlinarith
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- The wire count for `2 k` inputs and `lowerBudget k` gates fits in `2 ^ (k + 2)`. -/
theorem lowerBudget_wire_bound (k : ℕ) (hk : 64 ≤ k) :
    k + k + lowerBudget k + 1 ≤ 2 ^ (k + 2) := by
  have hq : lowerBudget k ≤ 2 ^ k := Nat.div_le_self _ _
  have hs := square_le_exponential k hk
  simp only [Nat.pow_succ]
  nlinarith

/-- **Counting step.** If the ordered-syntax budget for `q` gates is smaller than the number of
distinct powers `maxTransientDepth g + cyclePeriod g`, some power below `maxTransientDepth g +
cyclePeriod g` has no circuit with at most `q` gates. -/
theorem exists_hard_power_of_budget_lt {n : ℕ} (g : BitString n → BitString n) (q : ℕ)
    (large : signature.orderedBudget n n q < maxTransientDepth g + cyclePeriod g) :
    ∃ T < maxTransientDepth g + cyclePeriod g,
      ∀ out : Circuit signature n n, out.Computes interpretation g^[T] → q < out.size := by
  classical
  let family := Finset.univ.image
    (fun i : Fin (maxTransientDepth g + cyclePeriod g) => g^[i.val])
  have hcard : family.card = maxTransientDepth g + cyclePeriod g := by
    rw [Finset.card_image_of_injective _ (iterate_injective_below g)]
    simp
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := q)
    interpretation family (by rw [hcard]; exact large)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨i.val, i.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by omega) hcomp

/-- An explicit exponent form of the counting step, via `boolean_orderedBudget_le_pow`. -/
theorem exists_hard_power {n : ℕ} (g : BitString n → BitString n) (q h : ℕ)
    (hw : n + q + 1 ≤ 2 ^ h)
    (large : 2 ^ (3 * q + h * (2 * q + n + 1)) < maxTransientDepth g + cyclePeriod g) :
    ∃ T < maxTransientDepth g + cyclePeriod g,
      ∀ out : Circuit signature n n, out.Computes interpretation g^[T] → q < out.size :=
  exists_hard_power_of_budget_lt g q
    ((boolean_orderedBudget_le_pow n n q h hw).trans_lt large)

end Cslib.Circuits.Boolean.Iteration
