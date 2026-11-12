/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Data.List.Blocks

/-!
# Search-tree recurrences and branching-vector bounds

A branching algorithm that splits an instance of measure `n` into subproblems of measures at most
`n - a₁, …, n - a_b` (with positive integer decreases `aᵢ > 0`) generates a search tree whose size
is governed by the characteristic sum `∑ᵢ r ^ (-aᵢ)` (`Cslib.BranchingVector.charSum`). Whenever
`1 ≤ r` satisfies `charSum steps r ≤ 1`, a recurrence satisfying
`T n ≤ max C (∑_{d ∈ steps, d ≤ n} T (n - d))` at every `n`, with `C ≥ 0`, satisfies
`T n ≤ C * r ^ n` (`Cslib.BranchingVector.BranchingRecurrence.le_mul_pow`).

For explicit multi-way search trees (`Cslib.BranchingVector.BranchingTree`) where every non-leaf
expansion decreases `measure` by at least some sublist of `steps` and `1 ≤ r` satisfies
`charSum steps r ≤ 1`:
* the number of leaves is at most `r ^ measure s` (`BranchingTree.leafCount_le_pow`);
* the total number of internal and leaf nodes is at most `(measure s + 1) * r ^ measure s`
  (`BranchingTree.nodeCount_le_mul_pow`);
* per-node overhead `nodeWork ≤ W` separates multiplicatively as
  `workCost nodeWork s ≤ W * nodeCount s` and
  `(workCost nodeWork s : ℝ) ≤ W * (measure s + 1) * r ^ measure s`
  (`BranchingTree.workCost_le_mul_nodeCount`, `BranchingTree.workCost_le_mul_pow`).

Closed-form branching factors are supplied for binary splits `[1, 1]` (`r = 2`), Fibonacci splits
`[1, 2]` (`goldenBranchFactor = (1 + √5) / 2`), and `k`-clause prefix splits `[1, 2, …, k]`
(`prefixBranchFactor k = 2 - (1 / 2) ^ k < 2` for `k ≥ 1`).

## Main definitions

* `Cslib.BranchingVector.charSum`: characteristic sum `∑_{d ∈ steps} r ^ (-d)`.
* `Cslib.BranchingVector.BranchingRecurrence`: abstract positive-decrease search-tree recurrence.
* `Cslib.BranchingVector.BranchingTree`: terminating multi-way search tree with measure decreases,
  leaves, leaf/node counts, and per-node work cost.
* `Cslib.BranchingVector.goldenBranchFactor`, `Cslib.BranchingVector.prefixSteps`,
  `Cslib.BranchingVector.prefixBranchFactor`: closed-form branching vectors and factors.

## Main results

* `Cslib.BranchingVector.BranchingRecurrence.le_mul_pow`,
  `Cslib.BranchingVector.BranchingRecurrence.le_pow`: generic `r ^ n` recurrence upper bound.
* `Cslib.BranchingVector.BranchingTree.leafCount_le_pow`,
  `Cslib.BranchingVector.BranchingTree.nodeCount_le_mul_pow`,
  `Cslib.BranchingVector.BranchingTree.workCost_le_mul_pow`: search-tree leaf, node, and separated
  per-node work bounds.
* `Cslib.BranchingVector.BranchingTree.iff_exists_leaf`,
  `Cslib.BranchingVector.BranchingTree.sum_leaves_eq`,
  `Cslib.BranchingVector.BranchingTree.le_sum_leaves`: whole-tree predicate transport and additive
  or subadditive leaf aggregation.
* `Cslib.BranchingVector.charSum_fibonacci`,
  `Cslib.BranchingVector.charSum_prefixSteps_le_one`: closed-form `[1, 2]` and `[1, …, k]` bounds.

## References

* [F. V. Fomin, D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010]
-/

public section

namespace Cslib.BranchingVector

/-! ### Characteristic sums -/

/-- Characteristic sum `∑_{d ∈ steps} r ^ (-(d : ℝ))` of a branching vector `steps` at base `r`. -/
@[expose] noncomputable def charSum (steps : List ℕ) (r : ℝ) : ℝ :=
  (steps.map fun d : ℕ => r ^ (-(d : ℝ))).sum

@[simp] theorem charSum_nil (r : ℝ) : charSum [] r = 0 := rfl

@[simp] theorem charSum_cons (d : ℕ) (steps : List ℕ) (r : ℝ) :
    charSum (d :: steps) r = r ^ (-(d : ℝ)) + charSum steps r := by
  simp only [charSum, List.map_cons, List.sum_cons]

@[simp] theorem charSum_append (s₁ s₂ : List ℕ) (r : ℝ) :
    charSum (s₁ ++ s₂) r = charSum s₁ r + charSum s₂ r := by
  simp only [charSum, List.map_append, List.sum_append]

/-- For `r ≥ 0`, `r ^ (-(d : ℝ))` agrees with `(r⁻¹) ^ d`. -/
theorem rpow_neg_natCast_eq_inv_pow {r : ℝ} (hr : 0 ≤ r) (d : ℕ) :
    r ^ (-(d : ℝ)) = (r⁻¹) ^ d := by
  rw [Real.rpow_neg hr, Real.rpow_natCast, inv_pow]

/-- For `r ≥ 0`, `charSum steps r` rewrites as the elementary inverse-power sum `∑ (r⁻¹) ^ d`. -/
theorem charSum_eq_sum_inv_pow (steps : List ℕ) {r : ℝ} (hr : 0 ≤ r) :
    charSum steps r = (steps.map fun d : ℕ => (r⁻¹) ^ d).sum := by
  unfold charSum
  congr 1
  exact List.map_congr_left fun d _ => rpow_neg_natCast_eq_inv_pow hr d

/-- Characteristic sums are nonnegative at nonnegative bases. -/
theorem charSum_nonneg (steps : List ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ charSum steps r := by
  rw [charSum_eq_sum_inv_pow steps hr]
  exact List.sum_nonneg fun x hx => by
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hx
    positivity

/-- Taking a sublist of branches can only decrease the characteristic sum for `r ≥ 0`. -/
theorem charSum_sublist {s₁ s₂ : List ℕ} (hsub : List.Sublist s₁ s₂) {r : ℝ} (hr : 0 ≤ r) :
    charSum s₁ r ≤ charSum s₂ r := by
  induction hsub with
  | slnil => exact le_rfl
  | cons d _ ih =>
    rw [charSum_cons]
    have hd : 0 ≤ r ^ (-(d : ℝ)) := by
      rw [rpow_neg_natCast_eq_inv_pow hr]
      positivity
    linarith
  | cons_cons d _ ih =>
    rw [charSum_cons, charSum_cons]
    linarith

/-- Filtering a branching vector does not increase its characteristic sum for `r ≥ 0`. -/
theorem charSum_filter_le (p : ℕ → Bool) (steps : List ℕ) {r : ℝ} (hr : 0 ≤ r) :
    charSum (steps.filter p) r ≤ charSum steps r :=
  charSum_sublist List.filter_sublist hr

/-- `charSum steps` is antitone on `(0, ∞)`. -/
theorem charSum_antitone (steps : List ℕ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle : r₁ ≤ r₂) :
    charSum steps r₂ ≤ charSum steps r₁ := by
  have hr₂ : 0 < r₂ := hr₁.trans_le hle
  rw [charSum_eq_sum_inv_pow steps hr₂.le, charSum_eq_sum_inv_pow steps hr₁.le]
  induction steps with
  | nil => simp only [List.map_nil, List.sum_nil, le_refl]
  | cons d rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hinv : r₂⁻¹ ≤ r₁⁻¹ := inv_anti₀ hr₁ hle
    have hpow : (r₂⁻¹) ^ d ≤ (r₁⁻¹) ^ d := pow_le_pow_left₀ (by positivity) hinv d
    linarith

/-! ### Generic branching-vector recurrence -/

/-- A recurrence inequality representing a tree of recursive calls where each call branching
on a node of size `n` spawns subproblems of size `n - d` for `d ∈ steps`.
The base cost is bounded by `C`. -/
structure BranchingRecurrence (T : ℕ → ℝ) (steps : List ℕ) (C : ℝ) : Prop where
  /-- Nonnegativity of the base factor `C`. -/
  base_nonneg : 0 ≤ C
  /-- Every branching decrease is strictly positive. -/
  steps_pos : ∀ d ∈ steps, 0 < d
  /-- Inductive step bound. -/
  step_le : ∀ n, ∀ S : ℕ → ℝ, (∀ m < n, T m ≤ S m) →
    T n ≤ max C ((steps.filter (· ≤ n)).map fun d : ℕ => S (n - d)).sum

namespace BranchingRecurrence

/-- Build a `BranchingRecurrence` directly from the self-referential inequality
`T n ≤ max C (∑_{d ∈ steps, d ≤ n} T (n - d))` at every `n`. -/
theorem of_step {T : ℕ → ℝ} {steps : List ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hpos : ∀ d ∈ steps, 0 < d)
    (hstep : ∀ n, T n ≤ max C ((steps.filter (· ≤ n)).map fun d : ℕ => T (n - d)).sum) :
    BranchingRecurrence T steps C where
  base_nonneg := hC
  steps_pos := hpos
  step_le n S hS := (hstep n).trans <| max_le_max le_rfl <|
    List.sum_le_sum fun d hd => by
      obtain ⟨hd_mem, hd_le⟩ := List.mem_filter.mp hd
      exact hS (n - d) (Nat.sub_lt_of_pos_le (hpos d hd_mem) (of_decide_eq_true hd_le))

private theorem sum_pow_sub_eq {steps : List ℕ} {r : ℝ} (hr : 0 < r) (n : ℕ)
    (hle : ∀ d ∈ steps, d ≤ n) :
    (steps.map fun d : ℕ => r ^ (n - d)).sum = r ^ n * charSum steps r := by
  rw [charSum_eq_sum_inv_pow steps hr.le, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun d hd => ?_
  have hd_le : d ≤ n := hle d hd
  have hr_ne : r ≠ 0 := hr.ne'
  calc
    r ^ (n - d) = r ^ (n - d) * (r ^ d * (r⁻¹) ^ d) := by
      rw [← mul_pow, mul_inv_cancel₀ hr_ne, one_pow, mul_one]
    _ = (r ^ (n - d) * r ^ d) * (r⁻¹) ^ d := by ring
    _ = r ^ n * (r⁻¹) ^ d := by rw [← pow_add, Nat.sub_add_cancel hd_le]

/-- **Generic branching-vector theorem.** If `1 ≤ r` satisfies `charSum steps r ≤ 1`, then every
`BranchingRecurrence T steps C` satisfies `T n ≤ C * r ^ n` for all `n`. -/
theorem le_mul_pow {T : ℕ → ℝ} {steps : List ℕ} {C : ℝ}
    (hrec : BranchingRecurrence T steps C) {r : ℝ} (hr : 1 ≤ r)
    (hchar : charSum steps r ≤ 1) (n : ℕ) :
    T n ≤ C * r ^ n := by
  have hr_pos : 0 < r := by positivity
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    refine (hrec.step_le n (fun m => C * r ^ m) ih).trans ?_
    rw [max_le_iff]
    constructor
    · exact (mul_one C).symm.trans_le <| mul_le_mul_of_nonneg_left (one_le_pow₀ hr) hrec.base_nonneg
    · rw [List.sum_map_mul_left,
        sum_pow_sub_eq hr_pos n (fun d hd => of_decide_eq_true (List.mem_filter.mp hd).2)]
      have hfilt : charSum (steps.filter (· ≤ n)) r ≤ 1 :=
        (charSum_filter_le (· ≤ n) steps hr_pos.le).trans hchar
      have hCr : 0 ≤ C * r ^ n := mul_nonneg hrec.base_nonneg (by positivity)
      calc
        C * (r ^ n * charSum (steps.filter (· ≤ n)) r)
            = (C * r ^ n) * charSum (steps.filter (· ≤ n)) r := by ring
        _ ≤ (C * r ^ n) * 1 := mul_le_mul_of_nonneg_left hfilt hCr
        _ = C * r ^ n := mul_one _

/-- Unit-base specialization `T n ≤ r ^ n` when `C = 1`. -/
theorem le_pow {T : ℕ → ℝ} {steps : List ℕ}
    (hrec : BranchingRecurrence T steps 1) {r : ℝ} (hr : 1 ≤ r)
    (hchar : charSum steps r ≤ 1) (n : ℕ) :
    T n ≤ r ^ n := by
  simpa only [one_mul] using hrec.le_mul_pow hr hchar n

end BranchingRecurrence

/-! ### Terminating multi-way search trees with separate per-node work -/

/-- A terminating multi-way search tree on states `σ` with integer measure `measure` and positive
step vector `steps`. Every non-leaf state `s` expands into `children s` whose measure drops dominate
some sublist of `steps`. -/
structure BranchingTree (σ : Type*) where
  /-- Whether a state is a leaf of the search tree. -/
  isLeaf : σ → Bool
  /-- Child states generated when expanding an internal state. -/
  children : σ → List σ
  /-- Nonnegative complexity measure decreasing along every branch. -/
  measure : σ → ℕ
  /-- Nominal branching vector of positive measure decreases. -/
  steps : List ℕ
  /-- Every entry of `steps` is strictly positive. -/
  steps_pos : ∀ d ∈ steps, 0 < d
  /-- Expanding a non-leaf state decreases `measure` by at least some sublist of `steps`. -/
  children_steps : ∀ s, isLeaf s = false →
    ∃ steps', List.Sublist steps' steps ∧
      List.Forall₂ (fun child d => measure child + d ≤ measure s) (children s) steps'

namespace BranchingTree

variable {σ : Type*} (T : BranchingTree σ)

private theorem forall₂_imp_left_mem {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => nomatch hx
  | cons hxy _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨y, hy, hry⟩ := ih hx'
      exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

private theorem attach_flatMap_val {α β : Type*} (xs : List α) (f : α → List β) :
    (xs.attach.flatMap fun x => f x.1) = xs.flatMap f := by
  rw [List.flatMap_def, List.flatMap_def, List.attach_map_val]

/-- Every child of a non-leaf state has strictly smaller `measure`. -/
theorem measure_child_lt {s child : σ} (hleaf : T.isLeaf s = false)
    (hmem : child ∈ T.children s) :
    T.measure child < T.measure s := by
  obtain ⟨steps', hsub, hrel⟩ := T.children_steps s hleaf
  obtain ⟨d, hd_mem, hle⟩ := forall₂_imp_left_mem hrel hmem
  have hd_pos : 0 < d := T.steps_pos d (hsub.subset hd_mem)
  omega

/-- Ordered list of leaves reached from `s` in the search tree `T`. -/
def leaves (s : σ) : List σ :=
  if h : T.isLeaf s = true then
    [s]
  else
    (T.children s).attach.flatMap fun ⟨c, hc⟩ =>
      have : T.measure c < T.measure s :=
        T.measure_child_lt (Bool.eq_false_iff.mpr h) hc
      leaves c
termination_by T.measure s

@[simp] theorem leaves_of_isLeaf {s : σ} (h : T.isLeaf s = true) :
    T.leaves s = [s] := by
  rw [leaves]
  simp only [h, ↓reduceDIte]

theorem leaves_of_not_isLeaf {s : σ} (h : T.isLeaf s = false) :
    T.leaves s = (T.children s).flatMap T.leaves := by
  conv_lhs => rw [leaves]
  rw [dite_eq_right (by simp only [h, Bool.false_eq_true, not_false_eq_true])]
  exact attach_flatMap_val (T.children s) T.leaves

/-- Every state in `T.leaves s` is a leaf. -/
theorem isLeaf_of_mem_leaves {s l : σ} (hl : l ∈ T.leaves s) : T.isLeaf l = true := by
  induction hm : T.measure s using Nat.strong_induction_on generalizing s with
  | ind m ih =>
    cases hleaf : T.isLeaf s
    · rw [T.leaves_of_not_isLeaf hleaf, List.mem_flatMap] at hl
      obtain ⟨c, hc, hlc⟩ := hl
      exact ih (T.measure c) (hm ▸ T.measure_child_lt hleaf hc) hlc rfl
    · rw [T.leaves_of_isLeaf hleaf, List.mem_singleton] at hl
      rwa [hl]

/-- Number of leaves in the search tree rooted at `s`. -/
@[expose] def leafCount (s : σ) : ℕ := (T.leaves s).length

@[simp] theorem leafCount_of_isLeaf {s : σ} (h : T.isLeaf s = true) :
    T.leafCount s = 1 := by
  simp only [leafCount, T.leaves_of_isLeaf h, List.length_singleton]

theorem leafCount_of_not_isLeaf {s : σ} (h : T.isLeaf s = false) :
    T.leafCount s = ((T.children s).map T.leafCount).sum := by
  simp only [leafCount, T.leaves_of_not_isLeaf h, List.length_flatMap]
  rfl

/-- Total number of nodes (internal nodes plus leaves) in the search tree rooted at `s`. -/
def nodeCount (s : σ) : ℕ :=
  if h : T.isLeaf s = true then
    1
  else
    1 + ((T.children s).attach.map fun ⟨c, hc⟩ =>
      have : T.measure c < T.measure s :=
        T.measure_child_lt (Bool.eq_false_iff.mpr h) hc
      nodeCount c).sum
termination_by T.measure s

@[simp] theorem nodeCount_of_isLeaf {s : σ} (h : T.isLeaf s = true) :
    T.nodeCount s = 1 := by
  rw [nodeCount]
  simp only [h, ↓reduceDIte]

theorem nodeCount_of_not_isLeaf {s : σ} (h : T.isLeaf s = false) :
    T.nodeCount s = 1 + ((T.children s).map T.nodeCount).sum := by
  conv_lhs => rw [nodeCount]
  rw [dite_eq_right (by simp only [h, Bool.false_eq_true, not_false_eq_true]),
    List.attach_map_val]

/-- Total work summed over all nodes of the search tree rooted at `s` for per-node cost
`nodeWork`. -/
def workCost (nodeWork : σ → ℕ) (s : σ) : ℕ :=
  if h : T.isLeaf s = true then
    nodeWork s
  else
    nodeWork s + ((T.children s).attach.map fun ⟨c, hc⟩ =>
      have : T.measure c < T.measure s :=
        T.measure_child_lt (Bool.eq_false_iff.mpr h) hc
      workCost nodeWork c).sum
termination_by T.measure s

@[simp] theorem workCost_of_isLeaf (nodeWork : σ → ℕ) {s : σ} (h : T.isLeaf s = true) :
    T.workCost nodeWork s = nodeWork s := by
  rw [workCost]
  simp only [h, ↓reduceDIte]

theorem workCost_of_not_isLeaf (nodeWork : σ → ℕ) {s : σ} (h : T.isLeaf s = false) :
    T.workCost nodeWork s = nodeWork s + ((T.children s).map (T.workCost nodeWork)).sum := by
  conv_lhs => rw [workCost]
  rw [dite_eq_right (by simp only [h, Bool.false_eq_true, not_false_eq_true]),
    List.attach_map_val]

/-- Reachability of subtree states from `s` in `T`. -/
inductive Reachable (s : σ) : σ → Prop
  | refl : Reachable s s
  | snoc {u c : σ} : Reachable s u → T.isLeaf u = false → c ∈ T.children u → Reachable s c

/-- Every leaf in `T.leaves s` is reachable from `s`. -/
theorem reachable_of_mem_leaves {s l : σ} (hl : l ∈ T.leaves s) : T.Reachable s l := by
  suffices ∀ u, T.Reachable s u → l ∈ T.leaves u → T.Reachable s l from this s .refl hl
  intro u hreach hlu
  induction hm : T.measure u using Nat.strong_induction_on generalizing u with
  | ind m ih =>
    cases hleaf : T.isLeaf u
    · rw [T.leaves_of_not_isLeaf hleaf, List.mem_flatMap] at hlu
      obtain ⟨c, hc, hlc⟩ := hlu
      exact ih (T.measure c) (hm ▸ T.measure_child_lt hleaf hc) c (hreach.snoc hleaf hc) hlc rfl
    · rw [T.leaves_of_isLeaf hleaf, List.mem_singleton] at hlu
      rwa [hlu]

/-- Whole-tree equivalence transport: if a property `P` is equivalent at every reachable internal
state to holding on at least one child, then `P s` holds iff `P` holds at some leaf in
`T.leaves s`. -/
theorem iff_exists_leaf {s : σ} {P : σ → Prop}
    (hstep : ∀ u, T.Reachable s u → T.isLeaf u = false → (P u ↔ ∃ c ∈ T.children u, P c)) :
    P s ↔ ∃ l ∈ T.leaves s, P l := by
  suffices ∀ u, T.Reachable s u → (P u ↔ ∃ l ∈ T.leaves u, P l) from this s .refl
  intro u hreach
  induction hm : T.measure u using Nat.strong_induction_on generalizing u with
  | ind m ih =>
    cases hleaf : T.isLeaf u
    · rw [hstep u hreach hleaf, T.leaves_of_not_isLeaf hleaf]
      simp only [List.mem_flatMap]
      constructor
      · rintro ⟨c, hc, hPc⟩
        obtain ⟨l, hl, hPl⟩ :=
          (ih (T.measure c) (hm ▸ T.measure_child_lt hleaf hc) c (hreach.snoc hleaf hc) rfl).mp hPc
        exact ⟨l, ⟨c, hc, hl⟩, hPl⟩
      · rintro ⟨l, ⟨c, hc, hl⟩, hPl⟩
        exact ⟨c, hc,
          (ih (T.measure c) (hm ▸ T.measure_child_lt hleaf hc) c (hreach.snoc hleaf hc) rfl).mpr
            ⟨l, hl, hPl⟩⟩
    · rw [T.leaves_of_isLeaf hleaf]
      simp only [List.mem_singleton, exists_eq_left]

/-- Additive weights conserved at every reachable internal expansion sum over `T.leaves s` to their
root value `w s`. -/
theorem sum_leaves_eq {s : σ} {w : σ → ℕ}
    (hadd : ∀ u, T.Reachable s u → T.isLeaf u = false → w u = ((T.children u).map w).sum) :
    ((T.leaves s).map w).sum = w s := by
  suffices ∀ u, T.Reachable s u → ((T.leaves u).map w).sum = w u from this s .refl
  intro u hreach
  induction hm : T.measure u using Nat.strong_induction_on generalizing u with
  | ind m ih =>
    cases hleaf : T.isLeaf u
    · rw [T.leaves_of_not_isLeaf hleaf, List.sum_map_flatMap,
        hadd u hreach hleaf]
      congr 1
      refine List.map_congr_left fun c hc => ?_
      exact ih (T.measure c) (hm ▸ T.measure_child_lt hleaf hc) c (hreach.snoc hleaf hc) rfl
    · simp only [T.leaves_of_isLeaf hleaf, List.map_singleton, List.sum_singleton]

/-- Subadditive weights (`w u ≤ ∑_{c ∈ children u} w c`, as in covering rather than partitioning
branching rules) are bounded above by their sum over `T.leaves s`. -/
theorem le_sum_leaves {s : σ} {w : σ → ℕ}
    (hsub : ∀ u, T.Reachable s u → T.isLeaf u = false → w u ≤ ((T.children u).map w).sum) :
    w s ≤ ((T.leaves s).map w).sum := by
  suffices ∀ u, T.Reachable s u → w u ≤ ((T.leaves u).map w).sum from this s .refl
  intro u hreach
  induction hm : T.measure u using Nat.strong_induction_on generalizing u with
  | ind m ih =>
    cases hleaf : T.isLeaf u
    · rw [T.leaves_of_not_isLeaf hleaf, List.sum_map_flatMap]
      refine (hsub u hreach hleaf).trans (List.sum_le_sum fun c hc => ?_)
      exact ih (T.measure c) (hm ▸ T.measure_child_lt hleaf hc) c (hreach.snoc hleaf hc) rfl
    · simp only [T.leaves_of_isLeaf hleaf, List.map_singleton, List.sum_singleton, le_refl]

private theorem sum_children_pow_le {r : ℝ} (hr : 1 ≤ r) {m : ℕ}
    {children : List σ} {steps' : List ℕ}
    (hrel : List.Forall₂ (fun child d => T.measure child + d ≤ m) children steps')
    {f : σ → ℝ} (hf : ∀ child ∈ children, f child ≤ r ^ T.measure child) :
    (children.map f).sum ≤ r ^ m * charSum steps' r := by
  have hr0 : 0 < r := by positivity
  induction hrel with
  | nil =>
    simp only [List.map_nil, List.sum_nil, charSum_nil, mul_zero, le_refl]
  | @cons child d cs ds hcd hrest ih =>
    have hc_le : f child ≤ r ^ T.measure child := hf child List.mem_cons_self
    have hpow_le : r ^ T.measure child ≤ r ^ (m - d) := pow_le_pow_right₀ hr (by omega)
    have hd_le : d ≤ m := by omega
    have hterm : r ^ (m - d) = r ^ m * r ^ (-(d : ℝ)) := by
      rw [rpow_neg_natCast_eq_inv_pow hr0.le]
      calc
        r ^ (m - d) = r ^ (m - d) * (r ^ d * (r⁻¹) ^ d) := by
          rw [← mul_pow, mul_inv_cancel₀ hr0.ne', one_pow, mul_one]
        _ = (r ^ (m - d) * r ^ d) * (r⁻¹) ^ d := by ring
        _ = r ^ m * (r⁻¹) ^ d := by rw [← pow_add, Nat.sub_add_cancel hd_le]
    have hrest_le := ih fun c hc => hf c (List.mem_cons_of_mem _ hc)
    rw [List.map_cons, List.sum_cons, charSum_cons, mul_add]
    linarith [hc_le.trans hpow_le]

/-- **Search-tree leaf bound.** If `1 ≤ r` and `charSum T.steps r ≤ 1`, then the search tree rooted
at `s` has at most `r ^ T.measure s` leaves. -/
theorem leafCount_le_pow {r : ℝ} (hr : 1 ≤ r) (hchar : charSum T.steps r ≤ 1) (s : σ) :
    (T.leafCount s : ℝ) ≤ r ^ T.measure s := by
  suffices ∀ m (s : σ), T.measure s = m → (T.leafCount s : ℝ) ≤ r ^ m from this _ s rfl
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro s hm
    cases hleaf : T.isLeaf s
    · rw [T.leafCount_of_not_isLeaf hleaf, Nat.cast_list_sum, List.map_map]
      obtain ⟨steps', hsub, hrel⟩ := T.children_steps s hleaf
      have hrel' : List.Forall₂ (fun child d => T.measure child + d ≤ m) (T.children s) steps' :=
        hm ▸ hrel
      have hsum := T.sum_children_pow_le hr hrel' (f := fun c => (T.leafCount c : ℝ)) fun c hc =>
        ih (T.measure c) (hm ▸ T.measure_child_lt hleaf hc) c rfl
      have hchar' : charSum steps' r ≤ 1 :=
        (charSum_sublist hsub (by linarith)).trans hchar
      have hrm : 0 ≤ r ^ m := by positivity
      calc
        ((T.children s).map ((Nat.cast : ℕ → ℝ) ∘ T.leafCount)).sum
            ≤ r ^ m * charSum steps' r := hsum
        _ ≤ r ^ m * 1 := mul_le_mul_of_nonneg_left hchar' hrm
        _ = r ^ m := mul_one _
    · rw [T.leafCount_of_isLeaf hleaf, Nat.cast_one]
      exact one_le_pow₀ hr

/-- **Search-tree node bound.** If `1 ≤ r` and `charSum T.steps r ≤ 1`, then the total number of
nodes (internal and leaf) in the search tree rooted at `s` is at most
`(T.measure s + 1) * r ^ T.measure s`. -/
theorem nodeCount_le_mul_pow {r : ℝ} (hr : 1 ≤ r) (hchar : charSum T.steps r ≤ 1) (s : σ) :
    (T.nodeCount s : ℝ) ≤ (T.measure s + 1 : ℝ) * r ^ T.measure s := by
  suffices ∀ m (s : σ), T.measure s = m → (T.nodeCount s : ℝ) ≤ (m + 1 : ℝ) * r ^ m from
    this _ s rfl
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro s hm
    have hrm1 : 1 ≤ r ^ m := one_le_pow₀ hr
    cases hleaf : T.isLeaf s
    · rw [T.nodeCount_of_not_isLeaf hleaf, Nat.cast_add, Nat.cast_one, Nat.cast_list_sum,
        List.map_map]
      rcases hcs : T.children s with _ | ⟨c₀, cs⟩
      · simp only [List.map_nil, List.sum_nil, add_zero]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      · obtain ⟨steps', hsub, hrel⟩ := T.children_steps s hleaf
        have hrel' : List.Forall₂ (fun child d => T.measure child + d ≤ m) (c₀ :: cs) steps' :=
          hm ▸ hcs ▸ hrel
        have hchild_bound : ∀ c ∈ (c₀ :: cs),
            ((Nat.cast : ℕ → ℝ) ∘ T.nodeCount) c ≤ (m : ℝ) * r ^ T.measure c := by
          intro c hc
          have hc_mem : c ∈ T.children s := by rwa [hcs]
          have hlt : T.measure c < m := hm ▸ T.measure_child_lt hleaf hc_mem
          have hle_m : (T.measure c + 1 : ℝ) ≤ m := by exact_mod_cast hlt
          have hih := ih (T.measure c) hlt c rfl
          exact hih.trans (mul_le_mul_of_nonneg_right hle_m (by positivity))
        have hsum1 : ((c₀ :: cs).map ((Nat.cast : ℕ → ℝ) ∘ T.nodeCount)).sum ≤
            ((c₀ :: cs).map fun c => (m : ℝ) * r ^ T.measure c).sum :=
          List.sum_le_sum hchild_bound
        have hfactor := List.sum_map_mul_left (c₀ :: cs) (fun c => r ^ T.measure c) (m : ℝ)
        have hsum2 := T.sum_children_pow_le hr hrel' (f := fun c => r ^ T.measure c)
          fun _ _ => le_rfl
        have hchar' : charSum steps' r ≤ 1 :=
          (charSum_sublist hsub (by linarith)).trans hchar
        have hmr : 0 ≤ (m : ℝ) * r ^ m := by positivity
        have htot : ((c₀ :: cs).map ((Nat.cast : ℕ → ℝ) ∘ T.nodeCount)).sum ≤ (m : ℝ) * r ^ m := by
          calc
            ((c₀ :: cs).map ((Nat.cast : ℕ → ℝ) ∘ T.nodeCount)).sum
                ≤ (m : ℝ) * ((c₀ :: cs).map fun c => r ^ T.measure c).sum := hfactor ▸ hsum1
            _ ≤ (m : ℝ) * (r ^ m * charSum steps' r) :=
                mul_le_mul_of_nonneg_left hsum2 (Nat.cast_nonneg m)
            _ = ((m : ℝ) * r ^ m) * charSum steps' r := by ring
            _ ≤ ((m : ℝ) * r ^ m) * 1 := mul_le_mul_of_nonneg_left hchar' hmr
            _ = (m : ℝ) * r ^ m := mul_one _
        nlinarith
    · rw [T.nodeCount_of_isLeaf hleaf, Nat.cast_one]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith

/-- **Separating per-node overhead.** If `nodeWork u ≤ W` at every state reachable from `s`, then
total tree work is at most `W * T.nodeCount s`. -/
theorem workCost_le_mul_nodeCount {nodeWork : σ → ℕ} {W : ℕ} {s : σ}
    (hwork : ∀ u, T.Reachable s u → nodeWork u ≤ W) :
    T.workCost nodeWork s ≤ W * T.nodeCount s := by
  suffices ∀ u, T.Reachable s u → T.workCost nodeWork u ≤ W * T.nodeCount u from this s .refl
  intro u hreach
  induction hm : T.measure u using Nat.strong_induction_on generalizing u with
  | ind m ih =>
    have hu : nodeWork u ≤ W := hwork u hreach
    cases hleaf : T.isLeaf u
    · rw [T.workCost_of_not_isLeaf nodeWork hleaf, T.nodeCount_of_not_isLeaf hleaf,
        Nat.mul_add, Nat.mul_one]
      refine Nat.add_le_add hu ?_
      have hchildren : ((T.children u).map (T.workCost nodeWork)).sum ≤
          ((T.children u).map fun c => W * T.nodeCount c).sum :=
        List.sum_le_sum fun c hc =>
          ih (T.measure c) (hm ▸ T.measure_child_lt hleaf hc) c (hreach.snoc hleaf hc) rfl
      rwa [List.sum_map_mul_left] at hchildren
    · rw [T.workCost_of_isLeaf nodeWork hleaf, T.nodeCount_of_isLeaf hleaf, Nat.mul_one]
      exact hu

/-- **Combined tree work bound.** Per-node work `≤ W` combined with `charSum T.steps r ≤ 1`
(`1 ≤ r`) bounds total tree work by `W * (T.measure s + 1) * r ^ T.measure s`. -/
theorem workCost_le_mul_pow {nodeWork : σ → ℕ} {W : ℕ} {s : σ}
    (hwork : ∀ u, T.Reachable s u → nodeWork u ≤ W) {r : ℝ} (hr : 1 ≤ r)
    (hchar : charSum T.steps r ≤ 1) :
    (T.workCost nodeWork s : ℝ) ≤ (W : ℝ) * (T.measure s + 1 : ℝ) * r ^ T.measure s := by
  have h1 : (T.workCost nodeWork s : ℝ) ≤ (W : ℝ) * (T.nodeCount s : ℝ) := by
    exact_mod_cast T.workCost_le_mul_nodeCount hwork
  have h2 := mul_le_mul_of_nonneg_left (T.nodeCount_le_mul_pow hr hchar s) (Nat.cast_nonneg W)
  linarith [show (W : ℝ) * ((T.measure s + 1 : ℝ) * r ^ T.measure s) =
    (W : ℝ) * (T.measure s + 1 : ℝ) * r ^ T.measure s by ring]

end BranchingTree

/-! ### Closed-form branching factors -/

/-- Binary `[1, 1]` branching has exact characteristic sum `1` at `r = 2`. -/
theorem charSum_binary : charSum [1, 1] 2 = 1 := by
  rw [charSum_eq_sum_inv_pow [1, 1] (by norm_num)]
  norm_num

/-- Golden-ratio Fibonacci branching factor `(1 + √5) / 2 ≈ 1.6180` for `[1, 2]`. -/
@[expose] noncomputable def goldenBranchFactor : ℝ := (1 + Real.sqrt 5) / 2

/-- `1 < goldenBranchFactor`. -/
theorem one_lt_goldenBranchFactor : 1 < goldenBranchFactor := by
  unfold goldenBranchFactor
  have h5 : (1 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- `goldenBranchFactor < 2` (in fact `< 5 / 3`). -/
theorem goldenBranchFactor_lt_two : goldenBranchFactor < 2 := by
  unfold goldenBranchFactor
  have h5 : Real.sqrt 5 < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- Fibonacci `[1, 2]` branching has exact characteristic sum `1` at `goldenBranchFactor`. -/
theorem charSum_fibonacci : charSum [1, 2] goldenBranchFactor = 1 := by
  have hg_pos : 0 < goldenBranchFactor := by linarith [one_lt_goldenBranchFactor]
  rw [charSum_eq_sum_inv_pow [1, 2] hg_pos.le]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_one]
  have hsq : goldenBranchFactor ^ 2 = goldenBranchFactor + 1 := by
    unfold goldenBranchFactor
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith
  field_simp [hg_pos.ne']
  linarith

/-- Prefix step vector `[1, 2, …, k]` arising from `k`-clause disjoint prefix branching. -/
@[expose] def prefixSteps (k : ℕ) : List ℕ := List.range' 1 k

/-- Every entry of `prefixSteps k` is strictly positive. -/
theorem prefixSteps_pos {k d : ℕ} (hd : d ∈ prefixSteps k) : 0 < d := by
  rw [prefixSteps, List.mem_range'_1] at hd
  omega

/-- `prefixSteps b` is a prefix (hence sublist) of `prefixSteps k` whenever `b ≤ k`. -/
theorem prefixSteps_sublist {b k : ℕ} (hbk : b ≤ k) :
    List.Sublist (prefixSteps b) (prefixSteps k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hbk
  rw [prefixSteps, prefixSteps, ← List.range'_append_1]
  exact (List.prefix_append _ _).sublist

/-- Closed-form sub-`2` branching factor `2 - (1 / 2) ^ k` dominating `prefixSteps k` (`k ≥ 1`).
For `k = 1, 2, 3` this gives `3 / 2`, `7 / 4`, `15 / 8`, all strictly below `2`. -/
@[expose] noncomputable def prefixBranchFactor (k : ℕ) : ℝ := 2 - (1 / 2 : ℝ) ^ k

/-- For `k ≥ 1`, `1 < prefixBranchFactor k`. -/
theorem one_lt_prefixBranchFactor {k : ℕ} (hk : 1 ≤ k) : 1 < prefixBranchFactor k := by
  unfold prefixBranchFactor
  have hpow : (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
    calc
      (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 2 := pow_one _
  linarith

/-- `prefixBranchFactor k < 2` for every `k`. -/
theorem prefixBranchFactor_lt_two (k : ℕ) : prefixBranchFactor k < 2 := by
  unfold prefixBranchFactor
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
  linarith

private theorem geom_inv_sum_mul_sub_one (r : ℝ) (hr : r ≠ 0) (k : ℕ) :
    (r - 1) * ((List.range' 1 k).map fun d : ℕ => (r⁻¹) ^ d).sum = 1 - (r⁻¹) ^ k := by
  induction k with
  | zero => simp only [List.range'_zero, List.map_nil, List.sum_nil, mul_zero, pow_zero, sub_self]
  | succ k ih =>
    rw [List.range'_1_concat, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Nat.add_comm 1 k, mul_add, ih]
    have h1 : (r - 1) * (r⁻¹) ^ (k + 1) = (r⁻¹) ^ k - (r⁻¹) ^ (k + 1) := by
      calc
        (r - 1) * (r⁻¹) ^ (k + 1) = r * ((r⁻¹) ^ k * r⁻¹) - (r⁻¹) ^ (k + 1) := by
          rw [pow_succ, sub_mul, one_mul, ← pow_succ]
        _ = (r * r⁻¹) * (r⁻¹) ^ k - (r⁻¹) ^ (k + 1) := by ring
        _ = (r⁻¹) ^ k - (r⁻¹) ^ (k + 1) := by rw [mul_inv_cancel₀ hr, one_mul]
    linarith

/-- **Closed-form `k`-clause branching bound.** For every `k ≥ 1`,
`charSum (prefixSteps k) (prefixBranchFactor k) ≤ 1`. -/
theorem charSum_prefixSteps_le_one {k : ℕ} (hk : 1 ≤ k) :
    charSum (prefixSteps k) (prefixBranchFactor k) ≤ 1 := by
  set r := prefixBranchFactor k
  have hr1 : 1 < r := one_lt_prefixBranchFactor hk
  have hr2 : r < 2 := prefixBranchFactor_lt_two k
  have hr0 : 0 < r := by linarith
  rw [charSum_eq_sum_inv_pow (prefixSteps k) hr0.le, prefixSteps]
  have hgeom := geom_inv_sum_mul_sub_one r hr0.ne' k
  have hinv_gt : (1 / 2 : ℝ) ≤ r⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hr0 hr2.le
  have hpow_gt : (1 / 2 : ℝ) ^ k ≤ (r⁻¹) ^ k :=
    pow_le_pow_left₀ (by norm_num) hinv_gt k
  have hsub : 1 - (r⁻¹) ^ k ≤ r - 1 := by
    have hr_def : r = 2 - (1 / 2 : ℝ) ^ k := rfl
    linarith
  have hr_sub_pos : 0 < r - 1 := by linarith
  nlinarith

end Cslib.BranchingVector
