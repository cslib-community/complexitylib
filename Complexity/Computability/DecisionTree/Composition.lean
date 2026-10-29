/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Cost

/-!
# Composition of decision trees

`bind` replaces each output leaf by a continuation. `substitute` replaces each query by a
Boolean-valued decision tree and continues according to its answer. These are executable tree
constructions, with exact evaluation and per-input cost laws. The input variables of different
subroutines may overlap, and repeated queries are charged each time; substitution does not cache
their answers.

The structural cost of substitution is bounded by the outer tree's weighted depth, charging
each query the inner tree's structural cost. This is generally sharper than multiplying by the
most expensive query. Minimizing over trees gives the usual deterministic composition upper
bound. The disjoint-block corollary allows a different finite coordinate type for every block,
including empty blocks. No multiplicative lower bound is asserted.

## Main definitions

* `Cslib.DecisionTree.bind`: replace output leaves by continuations.
* `Cslib.DecisionTree.substitute`: replace queries by Boolean-valued subroutines.

## Main results

* `Cslib.DecisionTree.eval_substitute`: query substitution computes function composition.
* `Cslib.DecisionTree.weightedCost_substitute`: exact input-dependent composition cost.
* `Cslib.DecisionTree.weightedDepth_substitute_le`: composition with heterogeneous query costs.
* `Cslib.DecisionTree.complexity_substitute_le`: a weighted bound using any outer decision tree.
* `Cslib.DecisionTree.complexity_substitute_le_mul`: the uniform shared-input composition bound.
* `Cslib.DecisionTree.complexity_blockCompose_le_mul`: the disjoint-block composition bound.
-/

public section

namespace Cslib.DecisionTree

variable {ι κ μ β γ δ : Type*}

/-- Replace each leaf labelled `b` by the continuation `k b`. -/
@[expose] def bind : DecisionTree ι β → (β → DecisionTree ι γ) → DecisionTree ι γ
  | leaf b, k => k b
  | node i left right, k => node i (left.bind k) (right.bind k)

@[simp] theorem leaf_bind (b : β) (k : β → DecisionTree ι γ) : (leaf b).bind k = k b := rfl

@[simp] theorem node_bind (i : ι) (left right : DecisionTree ι β)
    (k : β → DecisionTree ι γ) :
    (node i left right).bind k = node i (left.bind k) (right.bind k) := rfl

/-- Replacing each leaf by itself preserves the tree. -/
@[simp] theorem bind_leaf (t : DecisionTree ι β) : t.bind leaf = t := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [ihl, ihr]

/-- Successive leaf substitutions associate. -/
theorem bind_assoc (t : DecisionTree ι β) (k : β → DecisionTree ι γ)
    (l : γ → DecisionTree ι δ) : (t.bind k).bind l = t.bind (fun b => (k b).bind l) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [ihl, ihr]

/-- Evaluate the first tree, then its selected continuation on the same input. -/
@[simp] theorem eval_bind (t : DecisionTree ι β) (k : β → DecisionTree ι γ) (x : ι → Bool) :
    (t.bind k).eval x = (k (t.eval x)).eval x := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => cases h : x i <;> simp [h, ihl, ihr]

/-- Leaf substitution adds exactly the costs of the two executed computations. -/
theorem weightedCost_bind (t : DecisionTree ι β) (k : β → DecisionTree ι γ)
    (w : ι → ℕ) (x : ι → Bool) :
    (t.bind k).weightedCost w x =
      t.weightedCost w x + (k (t.eval x)).weightedCost w x := by
  induction t with
  | leaf => simp
  | node i left right ihl ihr =>
    cases h : x i <;> simp [h, ihl, ihr, Nat.add_right_comm]

/-- A uniform bound on continuation costs adds to the first tree's structural cost. -/
theorem weightedDepth_bind_le (t : DecisionTree ι β) (k : β → DecisionTree ι γ)
    (w : ι → ℕ) {d : ℕ} (hk : ∀ b, (k b).weightedDepth w ≤ d) :
    (t.bind k).weightedDepth w ≤ t.weightedDepth w + d := by
  induction t with
  | leaf b => simpa only [leaf_bind, weightedDepth_leaf, Nat.zero_add] using hk b
  | node i left right ihl ihr =>
    simp only [node_bind, weightedDepth_node]
    omega

/-- A uniform bound on continuation depths adds to the first tree's depth. -/
theorem depth_bind_le (t : DecisionTree ι β) (k : β → DecisionTree ι γ)
    {d : ℕ} (hk : ∀ b, (k b).depth ≤ d) : (t.bind k).depth ≤ t.depth + d := by
  simpa only [weightedDepth_const, Nat.mul_one] using
    t.weightedDepth_bind_le k (fun _ => 1) (fun b => by simpa using hk b)

/-- Replace a query of `i` by the Boolean subroutine `s i`, then follow its answer.
Every occurrence is replaced independently; answers are not memoized. -/
@[expose] def substitute : DecisionTree ι β → (ι → DecisionTree κ Bool) → DecisionTree κ β
  | leaf b, _ => leaf b
  | node i left right, s =>
      (s i).bind (fun b => cond b (right.substitute s) (left.substitute s))

@[simp] theorem substitute_leaf (b : β) (s : ι → DecisionTree κ Bool) :
    (leaf b).substitute s = leaf b := rfl

theorem substitute_node (i : ι) (left right : DecisionTree ι β)
    (s : ι → DecisionTree κ Bool) :
    (node i left right).substitute s =
      (s i).bind (fun b => cond b (right.substitute s) (left.substitute s)) := rfl

/-- Replacing queries by single-query trees is ordinary query relabelling. -/
@[simp] theorem substitute_mapQueries (t : DecisionTree ι β) (f : ι → κ) :
    t.substitute (fun i => node (f i) (leaf false) (leaf true)) = t.mapQueries f := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [substitute_node, mapQueries, ihl, ihr]

/-- Query substitution distributes over leaf substitution. -/
theorem substitute_bind (t : DecisionTree ι β) (k : β → DecisionTree ι γ)
    (s : ι → DecisionTree κ Bool) :
    (t.bind k).substitute s = (t.substitute s).bind (fun b => (k b).substitute s) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr =>
    simp only [node_bind, substitute_node, bind_assoc]
    congr 1
    funext b
    cases b <;> simp [ihl, ihr]

/-- Nested query substitutions associate, so subroutines may be compiled in stages. -/
theorem substitute_assoc (t : DecisionTree ι β) (s : ι → DecisionTree κ Bool)
    (r : κ → DecisionTree μ Bool) :
    (t.substitute s).substitute r = t.substitute (fun i => (s i).substitute r) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr =>
    rw [substitute_node, substitute_bind, substitute_node]
    congr 1
    funext b
    cases b <;> simp [ihl, ihr]

/-- Query substitution evaluates the outer tree on the answers supplied by the inner trees. -/
@[simp] theorem eval_substitute (t : DecisionTree ι β) (s : ι → DecisionTree κ Bool)
    (x : κ → Bool) : (t.substitute s).eval x = t.eval (fun i => (s i).eval x) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr =>
    rw [substitute_node, eval_bind, eval_node]
    cases (s i).eval x <;> simp [ihl, ihr]

/-- Composing trees that compute the supplied functions computes their function composition. -/
theorem Computes.substitute {t : DecisionTree ι β} {f : (ι → Bool) → β}
    (ht : t.Computes f) {s : ι → DecisionTree κ Bool} {g : ι → (κ → Bool) → Bool}
    (hs : ∀ i, (s i).Computes (g i)) :
    (t.substitute s).Computes (fun x => f (fun i => g i x)) := by
  intro x
  rw [eval_substitute, ht]
  congr 1
  funext i
  exact hs i x

/-- Exact cost of substitution: charge each outer query the cost of its subroutine on the
current input. Overlapping variables and repeated queries are both permitted. -/
theorem weightedCost_substitute (t : DecisionTree ι β) (s : ι → DecisionTree κ Bool)
    (w : κ → ℕ) (x : κ → Bool) :
    (t.substitute s).weightedCost w x =
      t.weightedCost (fun i => (s i).weightedCost w x) (fun i => (s i).eval x) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr =>
    rw [substitute_node, weightedCost_bind, weightedCost_node]
    cases (s i).eval x <;> simp [ihl, ihr, Nat.add_comm]

/-- Exact query count after substitution, with the executed inner query counts as weights. -/
theorem cost_substitute (t : DecisionTree ι β) (s : ι → DecisionTree κ Bool) (x : κ → Bool) :
    (t.substitute s).cost x =
      t.weightedCost (fun i => (s i).cost x) (fun i => (s i).eval x) :=
  t.weightedCost_substitute s (fun _ => 1) x

/-- Bound each inner computation by its weighted structural depth and add these bounds along
the outer tree. An inner tree's most expensive leaf need not select the most expensive
continuation, so this is an inequality. -/
theorem weightedDepth_substitute_le (t : DecisionTree ι β) (s : ι → DecisionTree κ Bool)
    (w : κ → ℕ) : (t.substitute s).weightedDepth w ≤
      t.weightedDepth (fun i => (s i).weightedDepth w) := by
  induction t with
  | leaf => exact le_rfl
  | node i left right ihl ihr =>
    rw [substitute_node, weightedDepth_node]
    refine ((s i).weightedDepth_bind_le _ w (d := max
      (left.weightedDepth (fun j => (s j).weightedDepth w))
      (right.weightedDepth (fun j => (s j).weightedDepth w))) ?_).trans_eq (Nat.add_comm _ _)
    intro b
    cases b
    · exact ihl.trans (le_max_left _ _)
    · exact ihr.trans (le_max_right _ _)

/-- Substitution depth is bounded by charging each outer query the depth of its subroutine. -/
theorem depth_substitute_le (t : DecisionTree ι β) (s : ι → DecisionTree κ Bool) :
    (t.substitute s).depth ≤ t.weightedDepth (fun i => (s i).depth) := by
  simpa only [weightedDepth_const, Nat.mul_one] using
    t.weightedDepth_substitute_le s (fun _ => 1)

/-- Any outer decision tree gives a composition bound weighted by the optimal inner depths.
The inner functions may all read the same input variables. -/
theorem complexity_substitute_le [Finite κ] {t : DecisionTree ι β} {f : (ι → Bool) → β}
    (ht : t.Computes f) (g : ι → (κ → Bool) → Bool) :
    complexity (fun x => f (fun i => g i x)) ≤ t.weightedDepth (fun i => complexity (g i)) := by
  classical
  choose s hs hd using fun i => exists_computes_depth_eq_complexity (g i)
  exact (complexity_le_depth (ht.substitute hs)).trans
    ((t.depth_substitute_le s).trans_eq (by simp only [hd]))

/-- If each inner function has complexity at most `d`, composition has complexity at most
the outer complexity times `d`. No disjointness of the inner inputs is required. -/
theorem complexity_substitute_le_mul [Finite ι] [Finite κ] (f : (ι → Bool) → β)
    (g : ι → (κ → Bool) → Bool) {d : ℕ} (hg : ∀ i, complexity (g i) ≤ d) :
    complexity (fun x => f (fun i => g i x)) ≤ complexity f * d := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact (complexity_substitute_le ht g).trans
    ((t.weightedDepth_le_depth_mul hg).trans_eq (congrArg (· * d) hd))

/-- A weighted bound for composition on disjoint, possibly differently sized finite blocks. -/
theorem complexity_blockCompose_le {κ : ι → Type*} [∀ i, Finite (κ i)]
    {t : DecisionTree ι β} {f : (ι → Bool) → β} (ht : t.Computes f)
    (g : (i : ι) → (κ i → Bool) → Bool) :
    complexity (fun x : (Σ i, κ i) → Bool => f (fun i => g i (fun j => x ⟨i, j⟩))) ≤
      t.weightedDepth (fun i => complexity (g i)) := by
  classical
  choose s hs hd using fun i => exists_computes_depth_eq_complexity (g i)
  let lifted (i : ι) : DecisionTree (Σ i, κ i) Bool := (s i).mapQueries (Sigma.mk i)
  have hlifted (i : ι) : (lifted i).Computes (fun x => g i (fun j => x ⟨i, j⟩)) := by
    intro x
    exact (eval_mapQueries (Sigma.mk i) (s i) x).trans (hs i _)
  exact (complexity_le_depth (ht.substitute hlifted)).trans
    ((t.depth_substitute_le lifted).trans_eq (by simp only [lifted, depth_mapQueries, hd]))

/-- Uniform-cost composition on disjoint finite blocks; empty blocks and constant functions
are included. The construction proves an upper bound only. -/
theorem complexity_blockCompose_le_mul {κ : ι → Type*} [Finite ι] [∀ i, Finite (κ i)]
    (f : (ι → Bool) → β) (g : (i : ι) → (κ i → Bool) → Bool) {d : ℕ}
    (hg : ∀ i, complexity (g i) ≤ d) :
    complexity (fun x : (Σ i, κ i) → Bool => f (fun i => g i (fun j => x ⟨i, j⟩))) ≤
      complexity f * d := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact (complexity_blockCompose_le ht g).trans
    ((t.weightedDepth_le_depth_mul hg).trans_eq (congrArg (· * d) hd))

end Cslib.DecisionTree
