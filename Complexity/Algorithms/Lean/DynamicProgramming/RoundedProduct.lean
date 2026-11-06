/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.DynamicProgramming.MinProduct
public import Mathlib.Data.Rat.Floor
public import Complexity.Foundations.Data.Rat.BinarySize
import Mathlib.Tactic

/-!
# Rounded-cost product approximation

The maximum-cost-member branch of [Wang2027], Theorem 2(2), PDF p. 8.
`MinProduct.run` is an executable dynamic program, and its minimum-product
representative loses at most the sum of the rounding errors in the cost factor.
The approximation theorem below derives the multiplicative product–sum guarantee;
it does not take an approximate optimizer as input.

This module does not assert the complete scheduling FPTAS or a binary machine
runtime. Cutoff-family enumeration, first-batch nonemptiness and the policy bridge
belong to the application; a bound on table states alone is not a bit-cost proof.

## Main results

* `run_approximation`: every choice is approximated by an actual retained witness.
* `rounded_le_bound`: rounded costs of bounded items have a uniform numerical bound.
* `branch_approximation`: concrete scaling and mandatory-member initialization.
* `branch_length_le`, `branch_budget`: uniform table-size and recurrence-work bounds.
* `run_product_binaryWidth_le`: binary operand growth of actual retained products.
* `branchScale_binaryWidth_le`, `rounded_binarySize_le`: binary scaling/key operands.
-/

public section
namespace Cslib.Algorithms.Lean.DynamicProgramming.MinProduct

variable {ι : Type*}

/-- Exact selected cost, with no rounding. -/
@[expose] def Entry.cost (c : ι → ℚ) (e : Entry ι) : ℚ := (e.selected.map c).sum

/-- Scale positive costs down to natural-number table keys. -/
@[expose] def rounded (c : ι → ℚ) (K : ℚ) (i : ι) : ℕ := ⌊c i / K⌋₊

/-- Each rounded value underestimates its original cost. -/
theorem rounded_lower (c : ι → ℚ) {K : ℚ} (hK : 0 < K)
    (hc : ∀ i, 0 ≤ c i) (i : ι) : K * rounded c K i ≤ c i := by
  have h := Nat.floor_le (div_nonneg (hc i) hK.le)
  have h' := (le_div_iff₀ hK).mp h
  simpa [rounded, mul_comm] using h'

/-- Each item loses less than one scaling unit. -/
theorem rounded_upper (c : ι → ℚ) {K : ℚ} (hK : 0 < K) (i : ι) :
    c i ≤ K * rounded c K i + K := by
  have h := Nat.lt_floor_add_one (c i / K)
  have := (div_lt_iff₀ hK).mp h
  dsimp [rounded]
  nlinarith

/-- Bounded original costs imply bounded rounded keys. -/
theorem rounded_le_bound (c : ι → ℚ) {K C : ℚ} (hK : 0 < K)
    {N : ℕ} (hN : C / K ≤ N) {i : ι} (hc : c i ≤ C) : rounded c K i ≤ N := by
  apply Nat.floor_le_of_le
  exact (div_le_div_of_nonneg_right hc hK.le).trans hN

private theorem choices_cost_bounds (c : ι → ℚ) (q : ι → ℚ) {K : ℚ}
    (hK : 0 < K) (hc : ∀ i, 0 ≤ c i) (initial : Entry ι)
    (hi₀ : K * initial.rounded ≤ initial.cost c)
    (hi₁ : initial.cost c ≤ K * initial.rounded + K)
    (items : List ι) {e : Entry ι}
    (he : e ∈ choices (rounded c K) q initial items) :
    K * e.rounded ≤ e.cost c ∧
      e.cost c ≤ K * e.rounded + (items.length + 1 : ℕ) * K ∧
      initial.cost c ≤ e.cost c := by
  induction items generalizing e with
  | nil =>
    have : e = initial := by simpa [choices] using he
    subst e
    exact ⟨hi₀, by simpa using hi₁, le_rfl⟩
  | cons i is ih =>
    change e ∈ extend i (rounded c K i) (q i) (choices (rounded c K) q initial is) at he
    simp only [extend, List.mem_append, List.mem_map] at he
    rcases he with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · obtain ⟨h₀,h₁,h₂⟩ := ih ha
      norm_num only [Nat.cast_add, Nat.cast_one] at h₁
      simp only [Entry.skip, Entry.cost, List.length_cons, Nat.cast_add, Nat.cast_one]
      exact ⟨h₀,by change a.cost c ≤ _; nlinarith,h₂⟩
    · obtain ⟨h₀,h₁,h₂⟩ := ih ha
      norm_num only [Nat.cast_add, Nat.cast_one] at h₁
      have hl := rounded_lower c hK hc i
      have hu := rounded_upper c hK i
      simp only [Entry.take, Entry.cost, List.map_cons, List.sum_cons,
        List.length_cons, Nat.cast_add, Nat.cast_one]
      change K * ((a.rounded : ℚ) + rounded c K i) ≤ c i + a.cost c ∧ _
      exact ⟨by nlinarith,by change c i + a.cost c ≤ _; nlinarith,
        by change initial.cost c ≤ c i + a.cost c; linarith [hc i]⟩

private theorem choices_product_bounds (z : ι → ℕ) (q : ι → ℚ) (hq₀ : ∀ i, 0 ≤ q i)
    (hq₁ : ∀ i, q i ≤ 1) (initial : Entry ι)
    (hi₀ : 0 ≤ initial.product) (hi₁ : initial.product ≤ 1)
    (items : List ι) {e : Entry ι} (he : e ∈ choices z q initial items) :
    0 ≤ e.product ∧ e.product ≤ 1 := by
  induction items generalizing e with
  | nil =>
    have : e = initial := by simpa [choices] using he
    subst e
    exact ⟨hi₀,hi₁⟩
  | cons i is ih =>
    change e ∈ extend i (z i) (q i) (choices z q initial is) at he
    simp only [extend, List.mem_append, List.mem_map] at he
    rcases he with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · obtain ⟨h₀,h₁⟩ := ih ha
      exact ⟨mul_nonneg (hq₀ i) h₀,
        (mul_le_mul_of_nonneg_right (hq₁ i) h₀).trans (by simpa using h₁)⟩
    · change 0 ≤ a.product ∧ a.product ≤ 1
      exact ih ha

/-- Product–sum objective for the selected portion of the second batch. `E` is
its forced cost and `f` the failure product of the forced first batch. -/
@[expose] def Entry.gain (c : ι → ℚ) (E f : ℚ) (e : Entry ι) : ℚ :=
  (E + e.cost c) * (1 - f * e.product)

/-- The actual compressed dynamic program approximates every comparison choice
in the maximum-cost-member branch. The initial mandatory member supplies the
lower bound on comparison cost; the scaling condition bounds the total loss.
All conclusions concern returned witnesses, rather than an assumed approximation
oracle. Feasibility of the corresponding first batch is a separate application fact. -/
theorem run_approximation (c q : ι → ℚ) {K ε E f : ℚ}
    (hK : 0 < K) (hc : ∀ i, 0 ≤ c i)
    (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∀ i, q i ≤ 1)
    (hε₀ : 0 ≤ ε) (hE : 0 ≤ E) (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1)
    (initial : Entry ι) (hi₀ : K * initial.rounded ≤ initial.cost c)
    (hi₁ : initial.cost c ≤ K * initial.rounded + K)
    (hip₀ : 0 ≤ initial.product) (hip₁ : initial.product ≤ 1)
    (items : List ι) (hscale : (items.length + 1 : ℕ) * K ≤ ε * initial.cost c)
    {e : Entry ι} (he : e ∈ choices (rounded c K) q initial items) :
    ∃ d ∈ run (rounded c K) q initial items,
      d.rounded = e.rounded ∧ d.product ≤ e.product ∧
      (1 - ε) * e.gain c E f ≤ d.gain c E f := by
  obtain ⟨d,hd,hkey,hprod⟩ := run_dominates (rounded c K) q initial hq₀ items he
  have hd' := run_sound (rounded c K) q initial items hd
  obtain ⟨he₀,he₁,he₂⟩ := choices_cost_bounds c q hK hc initial hi₀ hi₁ items he
  obtain ⟨hd₀,hd₁,hd₂⟩ := choices_cost_bounds c q hK hc initial hi₀ hi₁ items hd'
  obtain ⟨hep₀,hep₁⟩ := choices_product_bounds (rounded c K) q hq₀ hq₁ initial hip₀ hip₁ items he
  obtain ⟨hdp₀,hdp₁⟩ := choices_product_bounds (rounded c K) q hq₀ hq₁ initial hip₀ hip₁ items hd'
  have hcost : (1 - ε) * (E + e.cost c) ≤ E + d.cost c := by
    rw [hkey] at hd₀
    have hεcost := mul_le_mul_of_nonneg_left he₂ hε₀
    nlinarith
  have hfac : 1 - f * e.product ≤ 1 - f * d.product := by nlinarith
  have hfac₀ : 0 ≤ 1 - f * e.product := by
    have := (mul_le_mul_of_nonneg_right hf₁ hep₀).trans (by simpa using hep₁)
    linarith
  have hiCost : 0 ≤ initial.cost c := (mul_nonneg hK.le (Nat.cast_nonneg _)).trans hi₀
  have hdCost : 0 ≤ E + d.cost c := by linarith
  refine ⟨d,hd,hkey,hprod,?_⟩
  unfold Entry.gain
  calc
    (1 - ε) * ((E + e.cost c) * (1 - f * e.product)) =
        ((1 - ε) * (E + e.cost c)) * (1 - f * e.product) := by ring
    _ ≤ (E + d.cost c) * (1 - f * e.product) :=
      mul_le_mul_of_nonneg_right hcost hfac₀
    _ ≤ (E + d.cost c) * (1 - f * d.product) :=
      mul_le_mul_of_nonneg_left hfac hdCost

/-- Scaling used by the maximum-cost-member branch. The mandatory member is
counted in the number of potential rounding errors. -/
@[expose] def branchScale (c : ι → ℚ) (ε : ℚ) (r : ι) (items : List ι) : ℚ :=
  ε * c r / (items.length + 1 : ℕ)

/-- Initial state with the required maximum-cost member selected. -/
@[expose] def branchInitial (c : ι → ℚ) (ε : ℚ) (r : ι) (outside : ℚ)
    (items : List ι) : Entry ι :=
  ⟨rounded c (branchScale c ε r items) r, outside, [r]⟩

/-- The executable maximum-cost-member branch of the approximation scheme.
`outside` is the failure product of optional items too costly to select. -/
@[expose] def branch (c q : ι → ℚ) (ε : ℚ) (r : ι) (outside : ℚ)
    (items : List ι) : List (Entry ι) :=
  run (rounded c (branchScale c ε r items)) q (branchInitial c ε r outside items) items

/-- Concrete branch approximation, with scaling and initial rounding established
by the theorem. The comparison is any actual select/omit choice in this branch. -/
theorem branch_approximation (c q : ι → ℚ) {ε E f outside : ℚ} (r : ι)
    (hc : ∀ i, 0 ≤ c i) (hr : 0 < c r) (hε : 0 < ε)
    (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∀ i, q i ≤ 1)
    (hE : 0 ≤ E) (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1)
    (ho₀ : 0 ≤ outside) (ho₁ : outside ≤ 1) (items : List ι)
    {e : Entry ι} (he : e ∈ choices (rounded c (branchScale c ε r items)) q
      (branchInitial c ε r outside items) items) :
    ∃ d ∈ branch c q ε r outside items,
      d.rounded = e.rounded ∧ d.product ≤ e.product ∧
      (1 - ε) * e.gain c E f ≤ d.gain c E f := by
  have hn : (0 : ℚ) < (items.length + 1 : ℕ) := by positivity
  have hK : 0 < branchScale c ε r items := div_pos (mul_pos hε hr) hn
  apply run_approximation c q hK hc hq₀ hq₁ hε.le hE hf₀ hf₁
      (branchInitial c ε r outside items) _ _ ho₀ ho₁ items _ he
  · simpa [branchInitial, Entry.cost] using rounded_lower c hK hc r
  · simpa [branchInitial, Entry.cost] using rounded_upper c hK r
  · simp only [branchInitial, Entry.cost, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, branchScale]
    exact le_of_eq (mul_div_cancel₀ _ (ne_of_gt hn))

/-- The actual branch table has polynomially many states in the item count and
inverse tolerance. This is a state bound, independent of the numerical costs;
it does not by itself bound rational arithmetic in binary bit operations. -/
theorem branch_length_le (c q : ι → ℚ) {ε outside : ℚ} (r : ι)
    (hr : 0 < c r) (hε : 0 < ε) (items : List ι)
    (hcost : ∀ i ∈ items, c i ≤ c r) :
    (branch c q ε r outside items).length ≤
      (items.length + 1) * ⌈(items.length + 1 : ℕ) / ε⌉₊ + 1 := by
  let K := branchScale c ε r items
  let N := ⌈(items.length + 1 : ℕ) / ε⌉₊
  have hn : (0 : ℚ) < (items.length + 1 : ℕ) := by positivity
  have hK : 0 < K := div_pos (mul_pos hε hr) hn
  have hratio : c r / K = (items.length + 1 : ℕ) / ε := by
    dsimp [K,branchScale]
    field_simp
  have hN : c r / K ≤ N := by rw [hratio]; exact Nat.le_ceil _
  have hz (i : ι) (hi : c i ≤ c r) : rounded c K i ≤ N :=
    rounded_le_bound c hK hN hi
  have sumBound : ∀ xs : List ι, (∀ i ∈ xs, rounded c K i ≤ N) →
      (xs.map (rounded c K)).sum ≤ xs.length * N := by
    intro xs
    induction xs with
    | nil => simp
    | cons i is ih =>
      intro h
      have hi := h i (List.mem_cons_self ..)
      have hs := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hsum := sumBound items (fun i hi => hz i (hcost i hi))
  have hinit : (branchInitial c ε r outside items).rounded ≤ N := hz r le_rfl
  have hb := run_length_le (rounded c K) q (branchInitial c ε r outside items) items
  change (branch c q ε r outside items).length ≤ _ at hb
  change (branch c q ε r outside items).length ≤ (items.length + 1) * N + 1
  nlinarith

/-- Every state actually retained by the DP has linearly bounded rational
product operands. The bound uses binary numerator/denominator magnitudes, not
the number of rational multiplications alone. -/
theorem run_product_binaryWidth_le (z : ι → ℕ) (q : ι → ℚ)
    (initial : Entry ι) (items : List ι) {e : Entry ι}
    (he : e ∈ run z q initial items) :
    e.product.binaryWidth ≤ initial.product.binaryWidth +
      (items.map (fun i => (q i).binaryWidth)).sum := by
  have hchoices : ∀ (xs : List ι) (d : Entry ι), d ∈ choices z q initial xs →
      d.product.binaryWidth ≤ initial.product.binaryWidth +
        (xs.map (fun i => (q i).binaryWidth)).sum := by
    intro xs
    induction xs with
    | nil =>
      intro d hd
      have heq : d = initial := by simpa [choices] using hd
      subst d
      simp
    | cons i is ih =>
      intro d hd
      change d ∈ extend i (z i) (q i) (choices z q initial is) at hd
      simp only [extend, List.mem_append, List.mem_map] at hd
      rcases hd with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
      · have hm := Rat.binaryWidth_mul_le (q i) a.product
        have hh := ih a ha
        simp only [Entry.skip, List.map_cons, List.sum_cons]
        omega
      · have hh := ih a ha
        simp only [Entry.take, List.map_cons, List.sum_cons]
        omega
  exact hchoices items e (run_sound z q initial items he)

/-- The scaling operand has binary width additive in tolerance, maximum cost
and the binary item-count counter. Large encoded costs do not create a table
of their numerical size. -/
theorem branchScale_binaryWidth_le (c : ι → ℚ) (ε : ℚ) (r : ι) (items : List ι) :
    (branchScale c ε r items).binaryWidth ≤
      ε.binaryWidth + (c r).binaryWidth + (items.length + 1).size + 1 := by
  have hm := Rat.binaryWidth_mul_le ε (c r)
  have hd := Rat.binaryWidth_div_le (ε * c r) (items.length + 1 : ℕ)
  have hn := Rat.binaryWidth_natCast_le (items.length + 1)
  unfold branchScale
  omega

/-- Binary size of each actually computed rounded key, including the division
and flooring operands. -/
theorem rounded_binarySize_le (c : ι → ℚ) (ε : ℚ) (r i : ι) (items : List ι) :
    (rounded c (branchScale c ε r items) i).size ≤
      (c i).binaryWidth + ε.binaryWidth + (c r).binaryWidth +
        (items.length + 1).size + 1 := by
  have hf := Rat.size_floor_le (c i / branchScale c ε r items)
  have hd := Rat.binaryWidth_div_le (c i) (branchScale c ε r items)
  have hs := branchScale_binaryWidth_le c ε r items
  unfold rounded
  omega

private theorem branch_key_budget (c : ι → ℚ) {ε : ℚ} (r : ι)
    (hr : 0 < c r) (hε : 0 < ε) (m : ℕ) (hm : 1 ≤ ε * m)
    (items : List ι) (hcost : ∀ i ∈ items, c i ≤ c r) :
    (branchInitial c ε r 1 items).rounded +
      (items.map (rounded c (branchScale c ε r items))).sum ≤
        (items.length + 1) ^ 2 * m := by
  let N := (items.length + 1) * m
  have hn : (0 : ℚ) < (items.length + 1 : ℕ) := by positivity
  have hK : 0 < branchScale c ε r items := div_pos (mul_pos hε hr) hn
  have hratio : c r / branchScale c ε r items = (items.length + 1 : ℕ) / ε := by
    unfold branchScale
    field_simp
  have hN : c r / branchScale c ε r items ≤ N := by
    rw [hratio, div_le_iff₀ hε]
    dsimp [N]
    push_cast
    nlinarith
  have hz (i : ι) (hi : c i ≤ c r) :
      rounded c (branchScale c ε r items) i ≤ N := rounded_le_bound c hK hN hi
  have hsum : ∀ xs : List ι, (∀ i ∈ xs, c i ≤ c r) →
      (xs.map (rounded c (branchScale c ε r items))).sum ≤ xs.length * N := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
      intro h
      have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      have hi := hz i (h i (List.mem_cons_self ..))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hi := hz r le_rfl
  have hs := hsum items hcost
  change rounded c (branchScale c ε r items) r + _ ≤ _
  dsimp [N] at *
  nlinarith

/-- Uniform state and work bounds in an integer inverse-tolerance budget `m`.
The budget requires only `1 ≤ ε*m`; its value is not assumed polynomial in the
binary encoding of epsilon. The work component still counts rational operations;
`run_product_binaryWidth_le` bounds their product operands separately. -/
theorem branch_budget (c q : ι → ℚ) {ε outside : ℚ} (r : ι)
    (hr : 0 < c r) (hε : 0 < ε) (m : ℕ) (hm : 1 ≤ ε * m)
    (items : List ι) (hcost : ∀ i ∈ items, c i ≤ c r) :
    (branch c q ε r outside items).length ≤ (items.length + 1) ^ 2 * m + 1 ∧
    runWork (rounded c (branchScale c ε r items)) q
      (branchInitial c ε r outside items) items ≤
        1 + items.length * (32 * ((items.length + 1) ^ 2 * m + 2) ^ 2) := by
  have hb := branch_key_budget c r hr hε m hm items hcost
  constructor
  · exact (run_length_le _ _ _ _).trans (Nat.succ_le_succ hb)
  · exact runWork_le _ _ _ items _ hb

end Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
