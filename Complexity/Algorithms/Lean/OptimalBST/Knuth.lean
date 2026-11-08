/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.OptimalBST.Yao
public import Complexity.Algorithms.Lean.TimeM.Loops
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Optimal binary search trees in quadratic time

The dynamic program for optimal binary search trees fills the table of intervals `(i, i + d]` by
increasing length `d`. Each entry scans a window `lo, …, hi` of candidate roots `k` and keeps the
largest one minimizing `T(i, k - 1) + T(k, j)` (`cellM`). The cubic algorithm (`plainBST`) scans
every root `i + 1, …, j`. Knuth's algorithm (`knuthBST`) scans only
`root(i, j - 1), …, root(i + 1, j)`, the window allowed by the monotonicity of optimal roots.

Both algorithms return the optimal cost `optCost w 0 n` and the tree `optTree w 0 n` read off the
largest optimal roots: the cubic one for every weight (`ret_plainBST`), Knuth's one when the weight
satisfies the quadrangle inequality and is monotone on intervals (`ret_knuthBST`). Without these
hypotheses Knuth's algorithm can return a suboptimal cost; see the test module
`ComplexityTests.OptimalBST`.

## Cost model

`Cslib.Algorithms.Lean.TimeM` charges one unit per candidate root scanned, so a window
`lo, …, hi` costs `hi - lo + 1`. Table reads and writes, additions, comparisons of costs, the
weight `w` and the final tree extraction are free; the table is a function, not a RAM array. This
counts candidate-root evaluations; it is not a Word-RAM bound.
The cubic algorithm scans exactly `n (n + 1) (n + 2) / 6` candidates (`time_plainBST`). Knuth's
scans at most `2 n²` (`time_knuthBST_le`): along a diagonal the windows telescope, so diagonal `d`
costs at most `2 n` (`time_diagM_knuth_le`).

## Main definitions

* `Cslib.Algorithms.Lean.OptimalBST.plainBST`: the cubic dynamic program.
* `Cslib.Algorithms.Lean.OptimalBST.knuthBST`: Knuth's quadratic algorithm.
* `Cslib.Algorithms.Lean.OptimalBST.Solution.IsOptimal`: the output is a binary search tree of the
  returned cost, and no binary search tree is cheaper.

## Main results

* `Cslib.Algorithms.Lean.OptimalBST.ret_plainBST`, `isOptimal_plainBST`: correctness of the cubic
  algorithm, for every weight.
* `Cslib.Algorithms.Lean.OptimalBST.time_plainBST`: it scans exactly `n (n + 1) (n + 2) / 6`
  candidates.
* `Cslib.Algorithms.Lean.OptimalBST.ret_knuthBST`, `isOptimal_knuthBST`: correctness of Knuth's
  algorithm under the quadrangle inequality and interval monotonicity.
* `Cslib.Algorithms.Lean.OptimalBST.time_knuthBST_le`: it scans at most `2 n²` candidates.
* `Cslib.Algorithms.Lean.OptimalBST.knuthBST_knuthWeight`: Knuth's theorem for nonnegative access
  and failure weights.

## References

* [D. E. Knuth, *Optimum binary search trees*][Knuth1971]
* [F. F. Yao, *Efficient dynamic programming using quadrangle inequalities*][Yao1980]
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Section 15.5][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.OptimalBST

open Finset TimeM

variable {β : Type*}

/-! ### Tables and windows -/

/-- A table entry: a cost and a root. -/
@[ext]
structure Entry (β : Type*) where
  /-- The cost of the interval. -/
  cost : β
  /-- The chosen root. -/
  root : ℕ
  deriving DecidableEq

/-- A dynamic-programming table, indexed by the endpoints `i, j` of the key interval
`i + 1, …, j`. -/
abbrev Table (β : Type*) := ℕ → ℕ → Entry β

/-- A rule choosing the window `lo, …, hi` of candidate roots for `(i, j]` from the table. -/
structure Window (β : Type*) where
  /-- The first candidate root. -/
  lo : Table β → ℕ → ℕ → ℕ
  /-- The last candidate root. -/
  hi : Table β → ℕ → ℕ → ℕ

/-- Every root `i + 1, …, j` (the cubic dynamic program). -/
@[expose] def Window.plain : Window β := ⟨fun _ i _ => i + 1, fun _ _ j => j⟩

/-- Knuth's window `root(i, j - 1), …, root(i + 1, j)`, or the only root `j` when `j = i + 1`. -/
@[expose] def Window.knuth : Window β :=
  ⟨fun T i j => if i + 1 < j then (T i (j - 1)).root else j,
    fun T i j => if i + 1 < j then (T (i + 1) j).root else j⟩

/-- Overwrite the entry of the interval `(i, i + d]`. -/
@[expose] def setCell (d : ℕ) (T : Table β) (i : ℕ) (e : Entry β) : Table β :=
  fun a b => if a = i ∧ b = i + d then e else T a b

theorem foldl_setCell (d : ℕ) (F : ℕ → Entry β) : ∀ (l : List ℕ) (U : Table β) (a b : ℕ),
    l.foldl (fun U i => setCell d U i (F i)) U a b = if a ∈ l ∧ b = a + d then F a else U a b
  | [], U, a, b => by simp only [List.foldl_nil, List.not_mem_nil, false_and, ↓reduceIte]
  | x :: l, U, a, b => by
    rw [List.foldl_cons, foldl_setCell d F l, setCell]
    simp only [List.mem_cons]
    split_ifs <;> grind

/-- The output of an optimal-BST algorithm: a cost and a tree. -/
structure Solution (β : Type*) where
  /-- The optimal cost. -/
  cost : β
  /-- A tree attaining it. -/
  tree : BinaryTree ℕ

/-! ### The scan of a window -/

section Scan

variable [LinearOrder β]

/-- Keep the cheaper of the current best entry and candidate `k`, preferring `k` on ties. -/
@[expose] def bestStep (c : ℕ → β) (best : Entry β) (k : ℕ) : Entry β :=
  if c k ≤ best.cost then ⟨c k, k⟩ else best

/-- Scan the candidates `lo, …, hi` for a largest minimizer of `c`, charging one unit per
candidate. -/
@[expose] def scanM (c : ℕ → β) (lo hi : ℕ) : TimeM ℕ (Entry β) := do
  ✓ (List.range' (lo + 1) (hi - lo)).foldlM (fun e k => do ✓ return bestStep c e k) ⟨c lo, lo⟩

private def ScanInv (c : ℕ → β) (lo hi : ℕ) (e : Entry β) : Prop :=
  lo ≤ e.root ∧ e.root ≤ hi ∧ e.cost = c e.root ∧ (∀ k, lo ≤ k → k ≤ hi → e.cost ≤ c k) ∧
    ∀ k, e.root < k → k ≤ hi → e.cost < c k

private theorem scanInv_foldl (c : ℕ → β) (lo : ℕ) : ∀ m,
    ScanInv c lo (lo + m) ((List.range' (lo + 1) m).foldl (bestStep c) ⟨c lo, lo⟩)
  | 0 => by
    refine ⟨le_rfl, le_rfl, rfl, fun k h₁ h₂ => ?_, fun k h₁ h₂ => ?_⟩
    · obtain rfl : k = lo := by omega
      exact le_rfl
    · exact absurd h₂ (by simp only [List.range'_zero, List.foldl_nil] at h₁; omega)
  | m + 1 => by
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := scanInv_foldl c lo m
    generalize (List.range' (lo + 1) m).foldl (bestStep c) ⟨c lo, lo⟩ = e at *
    unfold bestStep
    split_ifs with h
    · refine ⟨by dsimp only; omega, by dsimp only; omega, rfl, fun k hk₁ hk₂ => ?_,
        fun k hk₁ hk₂ => ?_⟩
      · rcases (show k ≤ lo + m ∨ k = lo + 1 + 1 * m by omega) with hk | rfl
        · exact h.trans (h₄ k hk₁ hk)
        · exact le_rfl
      · exact absurd hk₂ (by dsimp only at hk₁; omega)
    · have h' := not_le.1 h
      refine ⟨h₁, by omega, h₃, fun k hk₁ hk₂ => ?_, fun k hk₁ hk₂ => ?_⟩
      · rcases (show k ≤ lo + m ∨ k = lo + 1 + 1 * m by omega) with hk | rfl
        · exact h₄ k hk₁ hk
        · exact h'.le
      · rcases (show k ≤ lo + m ∨ k = lo + 1 + 1 * m by omega) with hk | rfl
        · exact h₅ k hk₁ hk
        · exact h'

theorem ret_scanM (c : ℕ → β) (lo hi : ℕ) :
    (scanM c lo hi).ret = (List.range' (lo + 1) (hi - lo)).foldl (bestStep c) ⟨c lo, lo⟩ := by
  simp only [scanM, ret_bind, ret_foldlM]
  rfl

/-- Scanning `lo, …, hi` costs `hi - lo + 1`. -/
theorem time_scanM (c : ℕ → β) (lo hi : ℕ) : (scanM c lo hi).time = hi - lo + 1 := by
  rw [scanM, time_bind, time_tick, time_foldlM_eq_sum _ (fun _ => 1) (fun _ _ => rfl),
    List.map_const', List.sum_replicate, List.length_range', smul_eq_mul, mul_one, add_comm]

end Scan

/-! ### The table algorithms -/

section Algorithm

variable [AddCommMonoid β] [LinearOrder β]

/-- The cost of root `k` for the keys `i + 1, …, j`, read from the table. -/
@[expose] def Table.candidate (T : Table β) (i j k : ℕ) : β := (T i (k - 1)).cost + (T k j).cost

/-- The entry for the keys `i + 1, …, j`, scanning the candidate roots `lo, …, hi`. -/
@[expose] def cellM (w : ℕ → ℕ → β) (T : Table β) (i j lo hi : ℕ) : TimeM ℕ (Entry β) := do
  let e ← scanM (T.candidate i j) lo hi
  return ⟨w i j + e.cost, e.root⟩

/-- Fill the diagonal of intervals `(i, i + d]` with `i + d ≤ n`, reading only `T`. -/
@[expose] def diagM (w : ℕ → ℕ → β) (W : Window β) (n d : ℕ) (T : Table β) : TimeM ℕ (Table β) :=
  (List.range (n + 1 - d)).foldlM (fun U i => do
    let e ← cellM w T i (i + d) (W.lo T i (i + d)) (W.hi T i (i + d))
    return setCell d U i e) T

/-- The table after filling the diagonals `1, …, d`. -/
@[expose] def tableM (w : ℕ → ℕ → β) (W : Window β) (n : ℕ) : ℕ → TimeM ℕ (Table β)
  | 0 => pure fun _ _ => ⟨0, 0⟩
  | d + 1 => do
    let T ← tableM w W n d
    diagM w W n (d + 1) T

/-- Fill the table for the keys `1, …, n` and read off the cost and the tree. -/
@[expose] def solveM (w : ℕ → ℕ → β) (W : Window β) (n : ℕ) : TimeM ℕ (Solution β) := do
  let T ← tableM w W n n
  return ⟨(T 0 n).cost, buildTree (fun i j => (T i j).root) n 0 n⟩

/-- The cubic dynamic program for optimal binary search trees. -/
@[expose] def plainBST (w : ℕ → ℕ → β) (n : ℕ) : TimeM ℕ (Solution β) := solveM w .plain n

/-- Knuth's quadratic algorithm for optimal binary search trees. -/
@[expose] def knuthBST (w : ℕ → ℕ → β) (n : ℕ) : TimeM ℕ (Solution β) := solveM w .knuth n

/-! ### Correctness -/

/-- `T` holds the optimal cost and the largest optimal root of every interval `(a, b]` with
`b ≤ n` and `b - a ≤ d`. -/
def Agrees (w : ℕ → ℕ → β) (n d : ℕ) (T : Table β) : Prop :=
  ∀ a b, b ≤ n → b - a ≤ d → T a b = ⟨optCost w a b, optRoot w a b⟩

/-- A window is valid if, whenever the table is correct on shorter intervals, it lies inside
`(i, j]` and contains the largest optimal root. -/
def Window.Valid (W : Window β) (w : ℕ → ℕ → β) (n : ℕ) : Prop :=
  ∀ d T i, Agrees w n d T → i + d + 1 ≤ n →
    i < W.lo T i (i + d + 1) ∧ W.lo T i (i + d + 1) ≤ optRoot w i (i + d + 1) ∧
      optRoot w i (i + d + 1) ≤ W.hi T i (i + d + 1) ∧ W.hi T i (i + d + 1) ≤ i + d + 1

theorem time_cellM (w : ℕ → ℕ → β) (T : Table β) (i j lo hi : ℕ) :
    (cellM w T i j lo hi).time = hi - lo + 1 := by
  rw [cellM, time_bind, time_scanM, time_pure, add_zero]

/-- A scan over a window containing the largest optimal root computes the correct entry. -/
theorem ret_cellM {w : ℕ → ℕ → β} {n d : ℕ} {T : Table β} (hT : Agrees w n d T) {i lo hi : ℕ}
    (hj : i + d + 1 ≤ n) (h₁ : i < lo) (h₂ : lo ≤ optRoot w i (i + d + 1))
    (h₃ : optRoot w i (i + d + 1) ≤ hi) (h₄ : hi ≤ i + d + 1) :
    (cellM w T i (i + d + 1) lo hi).ret = ⟨optCost w i (i + d + 1), optRoot w i (i + d + 1)⟩ := by
  have hc : ∀ k, i < k → k ≤ i + d + 1 →
      T.candidate i (i + d + 1) k = splitCost w i (i + d + 1) k := by
    intro k hk₁ hk₂
    rw [Table.candidate, splitCost, hT i (k - 1) (by omega) (by omega),
      hT k (i + d + 1) hj (by omega)]
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := scanInv_foldl (T.candidate i (i + d + 1)) lo (hi - lo)
  rw [show lo + (hi - lo) = hi by omega] at e₂ e₄ e₅
  simp only [cellM, ret_bind, ret_pure, ret_scanM]
  generalize (List.range' (lo + 1) (hi - lo)).foldl (bestStep (T.candidate i (i + d + 1)))
    ⟨T.candidate i (i + d + 1) lo, lo⟩ = e at *
  have hopt := optRoot_mem w (show i < i + d + 1 by omega)
  rw [mem_Ioc] at hopt
  -- `e.root` is a minimizer over the whole interval
  have hmin : ∀ k ∈ Ioc i (i + d + 1),
      splitCost w i (i + d + 1) e.root ≤ splitCost w i (i + d + 1) k := by
    intro k hk
    calc splitCost w i (i + d + 1) e.root = e.cost := by rw [e₃, hc _ (by omega) (by omega)]
      _ ≤ T.candidate i (i + d + 1) (optRoot w i (i + d + 1)) := e₄ _ h₂ h₃
      _ = splitCost w i (i + d + 1) (optRoot w i (i + d + 1)) := hc _ hopt.1 hopt.2
      _ ≤ splitCost w i (i + d + 1) k := splitCost_optRoot_le w hk
  have hle := le_optRoot w (mem_Ioc.2 ⟨by omega, by omega⟩) hmin
  have heq : e.root = optRoot w i (i + d + 1) := by
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have := e₅ _ hlt h₃
    rw [e₃, hc _ (by omega) (by omega), hc _ hopt.1 hopt.2] at this
    exact absurd (splitCost_optRoot_le w (mem_Ioc.2 ⟨by omega, by omega⟩)) (not_le.2 this)
  ext
  · rw [optCost_eq_optRoot w (by omega), ← heq, e₃, hc _ (by omega) (by omega)]
  · exact heq

theorem ret_diagM (w : ℕ → ℕ → β) (W : Window β) (n d : ℕ) (T : Table β) :
    (diagM w W n d T).ret = (List.range (n + 1 - d)).foldl (fun U i => setCell d U i
      (cellM w T i (i + d) (W.lo T i (i + d)) (W.hi T i (i + d))).ret) T := by
  rw [diagM, ret_foldlM]
  rfl

/-- Filling diagonal `d` costs the sum of its window lengths. -/
theorem time_diagM (w : ℕ → ℕ → β) (W : Window β) (n d : ℕ) (T : Table β) :
    (diagM w W n d T).time =
      ∑ i ∈ range (n + 1 - d), (W.hi T i (i + d) - W.lo T i (i + d) + 1) := by
  rw [diagM, time_foldlM_eq_sum _ (fun i => W.hi T i (i + d) - W.lo T i (i + d) + 1)
    (fun U i => by rw [time_bind, time_cellM, time_pure, add_zero])]
  rfl

theorem agrees_diagM {w : ℕ → ℕ → β} {W : Window β} {n d : ℕ} (hW : W.Valid w n) {T : Table β}
    (hT : Agrees w n d T) : Agrees w n (d + 1) (diagM w W n (d + 1) T).ret := by
  intro a b hb hab
  rw [ret_diagM, foldl_setCell]
  split_ifs with h
  · obtain ⟨ha, rfl⟩ := h
    rw [List.mem_range] at ha
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hW d T a hT (by omega)
    exact ret_cellM hT (by omega) h₁ h₂ h₃ h₄
  · exact hT a b hb (not_lt.1 fun hc => h ⟨List.mem_range.2 (by omega), by omega⟩)

theorem agrees_tableM {w : ℕ → ℕ → β} {W : Window β} {n : ℕ} (hW : W.Valid w n) :
    ∀ d, Agrees w n d (tableM w W n d).ret
  | 0 => fun a b _ hab => by
    rw [optCost_of_le w (by omega), optRoot_of_le w (by omega)]
    rfl
  | d + 1 => by
    rw [tableM, ret_bind]
    exact agrees_diagM hW (agrees_tableM hW d)

theorem Window.valid_plain (w : ℕ → ℕ → β) (n : ℕ) : (Window.plain : Window β).Valid w n := by
  intro d T i _ _
  have := mem_Ioc.1 (optRoot_mem w (show i < i + d + 1 by omega))
  exact ⟨Nat.lt_succ_self i, by simp only [Window.plain]; omega, this.2, le_rfl⟩

theorem ret_solveM {w : ℕ → ℕ → β} {W : Window β} {n : ℕ} (hW : W.Valid w n) :
    (solveM w W n).ret = ⟨optCost w 0 n, optTree w 0 n⟩ := by
  have hT := agrees_tableM hW n
  simp only [solveM, ret_bind, ret_pure]
  generalize (tableM w W n n).ret = T at hT
  have hR : ∀ a b, 0 ≤ a → a < b → b ≤ n → (T a b).root = optRoot w a b := fun a b _ _ hb => by
    rw [hT a b hb (by omega)]
  rw [hT 0 n le_rfl (by omega), optTree, Nat.sub_zero,
    buildTree_congr (R' := optRoot w) hR fun a b _ hab hb => hR a b (Nat.zero_le a) hab hb ▸
      optRoot_mem w hab]

theorem time_solveM (w : ℕ → ℕ → β) (W : Window β) (n : ℕ) :
    (solveM w W n).time = (tableM w W n n).time := by
  rw [solveM, time_bind, time_pure, add_zero]

/-- **Correctness of the cubic dynamic program**, for every weight: it returns the optimal cost and
the tree read off the largest optimal roots. -/
theorem ret_plainBST (w : ℕ → ℕ → β) (n : ℕ) :
    (plainBST w n).ret = ⟨optCost w 0 n, optTree w 0 n⟩ :=
  ret_solveM (Window.valid_plain w n)

/-! ### The cost of the cubic algorithm -/

private theorem sum_range_add_one_mul_two (m : ℕ) :
    (∑ e ∈ range m, (e + 1)) * 2 = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [sum_range_succ, add_mul, ih]; ring

private theorem six_mul_sum (n : ℕ) :
    6 * ∑ e ∈ range n, (n - e) * (e + 1) = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h₁ : ∑ e ∈ range (n + 1), (n + 1 - e) * (e + 1) =
        ∑ e ∈ range (n + 1), ((n - e) * (e + 1) + (e + 1)) :=
      sum_congr rfl fun e he => by
        rw [mem_range] at he
        rw [show n + 1 - e = (n - e) + 1 by omega, add_mul, one_mul]
    rw [h₁, sum_add_distrib, sum_range_succ (fun e => (n - e) * (e + 1)), Nat.sub_self, zero_mul,
      add_zero]
    have h₂ := sum_range_add_one_mul_two (n + 1)
    nlinarith [ih, h₂]

theorem time_tableM_plain (w : ℕ → ℕ → β) (n : ℕ) :
    ∀ d, (tableM w .plain n d).time = ∑ e ∈ range d, (n - e) * (e + 1)
  | 0 => rfl
  | d + 1 => by
    rw [tableM, time_bind, time_tableM_plain w n d, time_diagM, sum_range_succ]
    congr 1
    rw [← smul_eq_mul, ← card_range (n - d), ← sum_const]
    refine sum_congr (by congr 1; omega) fun i _ => ?_
    simp only [Window.plain]
    omega

/-- **The cubic dynamic program scans exactly `n (n + 1) (n + 2) / 6` candidate roots.** -/
theorem time_plainBST (w : ℕ → ℕ → β) (n : ℕ) :
    6 * (plainBST w n).time = n * (n + 1) * (n + 2) := by
  rw [plainBST, time_solveM, time_tableM_plain, six_mul_sum]

end Algorithm

/-! ### Knuth's algorithm -/

section Knuth

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

/-- Under the quadrangle inequality and interval monotonicity, Knuth's window is valid. -/
theorem Window.valid_knuth {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) (n : ℕ) : (Window.knuth : Window β).Valid w n := by
  intro d T i hT hj
  have hopt := mem_Ioc.1 (optRoot_mem w (show i < i + d + 1 by omega))
  rcases d with _ | e
  · have h : optRoot w i (i + 0 + 1) = i + 0 + 1 := by omega
    simp only [Window.knuth, add_zero, lt_irrefl, ↓reduceIte]
    simp only [add_zero] at h
    omega
  · have hmon := optRoot_mono hqi hmono (show i + 1 < i + (e + 1) + 1 by omega)
    rw [show i + (e + 1) + 1 - 1 = i + e + 1 by omega] at hmon
    have hlo : (T i (i + (e + 1))).root = optRoot w i (i + e + 1) := by
      rw [hT i (i + (e + 1)) (by omega) (by omega)]
      rfl
    have hhi : (T (i + 1) (i + (e + 1) + 1)).root = optRoot w (i + 1) (i + (e + 1) + 1) := by
      rw [hT (i + 1) (i + (e + 1) + 1) hj (by omega)]
    have h₁ := mem_Ioc.1 (optRoot_mem w (show i < i + e + 1 by omega))
    have h₂ := mem_Ioc.1 (optRoot_mem w (show i + 1 < i + (e + 1) + 1 by omega))
    simp only [Window.knuth, show i + 1 < i + (e + 1) + 1 by omega, ↓reduceIte,
      show i + (e + 1) + 1 - 1 = i + (e + 1) by omega, hlo, hhi]
    omega

/-- **Correctness of Knuth's algorithm** when the weight satisfies the quadrangle inequality and
is monotone on intervals. -/
theorem ret_knuthBST {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w) (hmono : MonotoneOnIntervals w)
    (n : ℕ) : (knuthBST w n).ret = ⟨optCost w 0 n, optTree w 0 n⟩ :=
  ret_solveM (Window.valid_knuth hqi hmono n)

private theorem sum_telescope (a : ℕ → ℕ) : ∀ m, (∀ i < m, a i ≤ a (i + 1)) →
    (∑ i ∈ range m, (a (i + 1) - a i + 1)) + a 0 = a m + m
  | 0, _ => by rw [sum_range_zero, zero_add, add_zero]
  | m + 1, h => by
    have ih := sum_telescope a m fun i hi => h i (by omega)
    have := h m (by omega)
    rw [sum_range_succ]
    omega

/-- **Knuth's telescoping bound**: under the hypotheses of `ret_knuthBST`, filling one diagonal
scans at most `2 n` candidate roots. -/
theorem time_diagM_knuth_le {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) {n d : ℕ} {T : Table β} (hT : Agrees w n d T) :
    (diagM w .knuth n (d + 1) T).time ≤ 2 * n := by
  rw [time_diagM]
  rcases d with _ | e
  · calc ∑ i ∈ range (n + 1 - (0 + 1)),
          ((Window.knuth : Window β).hi T i (i + (0 + 1)) -
            (Window.knuth : Window β).lo T i (i + (0 + 1)) + 1)
        = ∑ _i ∈ range (n + 1 - (0 + 1)), 1 :=
          sum_congr rfl fun i _ => by simp only [Window.knuth, zero_add, lt_irrefl, ↓reduceIte,
            Nat.sub_self]
      _ ≤ 2 * n := by rw [sum_const, card_range, smul_eq_mul, mul_one]; omega
  · obtain ⟨m, hm⟩ : ∃ m, m = n + 1 - (e + 1 + 1) := ⟨_, rfl⟩
    rw [← hm]
    let a : ℕ → ℕ := fun i => optRoot w i (i + e + 1)
    have hterm : ∀ i ∈ range m, (Window.knuth : Window β).hi T i (i + (e + 1 + 1)) -
        (Window.knuth : Window β).lo T i (i + (e + 1 + 1)) + 1 = a (i + 1) - a i + 1 := by
      intro i hi
      rw [mem_range] at hi
      have hlo : (T i (i + (e + 1 + 1) - 1)).root = a i := by
        rw [show i + (e + 1 + 1) - 1 = i + (e + 1) by omega, hT i (i + (e + 1)) (by omega)
          (by omega)]
        simp only [a]
        congr 1
      have hhi : (T (i + 1) (i + (e + 1 + 1))).root = a (i + 1) := by
        rw [hT (i + 1) (i + (e + 1 + 1)) (by omega) (by omega)]
        simp only [a]
        congr 1
        omega
      simp only [Window.knuth, show i + 1 < i + (e + 1 + 1) by omega, ↓reduceIte, hlo, hhi]
    rw [sum_congr rfl hterm]
    have ha : ∀ i < m, a i ≤ a (i + 1) := by
      intro i hi
      have hmon := optRoot_mono hqi hmono (show i + 1 < i + e + 2 by omega)
      rw [show i + e + 2 - 1 = i + e + 1 by omega] at hmon
      calc a i = optRoot w i (i + e + 1) := rfl
        _ ≤ optRoot w i (i + e + 2) := hmon.1
        _ ≤ optRoot w (i + 1) (i + e + 2) := hmon.2
        _ = a (i + 1) := by simp only [a]; congr 1; omega
    have htel := sum_telescope a m ha
    have h₀ := mem_Ioc.1 (optRoot_mem w (show 0 < 0 + e + 1 by omega))
    rcases Nat.eq_zero_or_pos m with rfl | hm₀
    · rw [sum_range_zero]
      omega
    · have hm' := mem_Ioc.1 (optRoot_mem w (show m < m + e + 1 by omega))
      change (∑ i ∈ range m, (a (i + 1) - a i + 1)) + optRoot w 0 (0 + e + 1) =
        optRoot w m (m + e + 1) + m at htel
      omega

/-- The first `d` diagonals of Knuth's algorithm scan at most `2 n d` candidate roots. -/
theorem time_tableM_knuth_le {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) (n : ℕ) : ∀ d, (tableM w .knuth n d).time ≤ 2 * n * d
  | 0 => by rw [tableM, time_pure]; exact Nat.zero_le _
  | d + 1 => by
    rw [tableM, time_bind]
    have h₁ := time_tableM_knuth_le hqi hmono n d
    have h₂ := time_diagM_knuth_le hqi hmono (agrees_tableM (Window.valid_knuth hqi hmono n) d)
    rw [mul_add, mul_one]
    exact add_le_add h₁ h₂

/-- **Knuth's speedup**: under the quadrangle inequality and interval monotonicity of the weight,
Knuth's algorithm scans at most `2 n²` candidate roots. -/
theorem time_knuthBST_le {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) (n : ℕ) : (knuthBST w n).time ≤ 2 * n ^ 2 := by
  rw [knuthBST, time_solveM, sq, ← mul_assoc]
  exact time_tableM_knuth_le hqi hmono n n

end Knuth

/-! ### Optimality of the output -/

section Optimal

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]

/-- A solution for the keys `1, …, n` is optimal for the weight `w` if its tree is a binary search
tree on these keys of the returned cost, and no binary search tree on them is cheaper. -/
def Solution.IsOptimal (w : ℕ → ℕ → β) (n : ℕ) (s : Solution β) : Prop :=
  IsBST 0 n s.tree ∧ treeCost w 0 n s.tree = s.cost ∧ ∀ t, IsBST 0 n t → s.cost ≤ treeCost w 0 n t

theorem isOptimal_optTree (w : ℕ → ℕ → β) (n : ℕ) :
    (⟨optCost w 0 n, optTree w 0 n⟩ : Solution β).IsOptimal w n :=
  ⟨isBST_optTree w (Nat.zero_le n), treeCost_optTree w (Nat.zero_le n),
    fun _ ht => optCost_le_treeCost w ht⟩

/-- The cubic dynamic program returns an optimal binary search tree, for every weight. -/
theorem isOptimal_plainBST (w : ℕ → ℕ → β) (n : ℕ) : (plainBST w n).ret.IsOptimal w n := by
  rw [ret_plainBST]
  exact isOptimal_optTree w n

end Optimal

section OptimalKnuth

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

/-- Knuth's algorithm returns an optimal binary search tree when the weight satisfies the
quadrangle inequality and is monotone on intervals. -/
theorem isOptimal_knuthBST {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) (n : ℕ) : (knuthBST w n).ret.IsOptimal w n := by
  rw [ret_knuthBST hqi hmono]
  exact isOptimal_optTree w n

/-- **Knuth's theorem** for nonnegative access weights `p` and failure weights `q`: the quadratic
algorithm returns an optimal binary search tree after scanning at most `2 n²` candidate roots. -/
theorem knuthBST_knuthWeight {p q : ℕ → β} (hp : ∀ k, 0 ≤ p k) (hq : ∀ g, 0 ≤ q g) (n : ℕ) :
    (knuthBST (knuthWeight p q) n).ret.IsOptimal (knuthWeight p q) n ∧
      (knuthBST (knuthWeight p q) n).time ≤ 2 * n ^ 2 :=
  ⟨isOptimal_knuthBST (quadrangleIneq_knuthWeight p q) (monotoneOnIntervals_knuthWeight hp hq) n,
    time_knuthBST_le (quadrangleIneq_knuthWeight p q) (monotoneOnIntervals_knuthWeight hp hq) n⟩

end OptimalKnuth

end Cslib.Algorithms.Lean.OptimalBST
