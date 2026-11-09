/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Foundations.Data.BitString.Balanced

/-!
# The deterministic query complexity of Deutsch–Jozsa

**The Deutsch–Jozsa problem** [Deutsch, Jozsa][DeutschJozsa1992], as stated in
[de Wolf, §2.4.1][deWolf2019]: the input `x ∈ {0,1}^N` is promised to be either *constant* or
*balanced*, with exactly `N/2` true bits (`Cslib.BitString.IsBalanced`). The goal is to decide
which. The library has no promise-problem type for query complexity. As for Bernstein–Vazirani and
Simon's problem, the lower bounds therefore take any total function that answers correctly on the
promise inputs (`Cslib.QueryComplexity.SolvesDeutschJozsa`: `true` on constant inputs, `false` on
balanced ones).

**Lower bound.** Over `N = 2m` positions every deterministic decision tree needs depth `m + 1`
(`Cslib.QueryComplexity.depth_ge_of_solvesDeutschJozsa`). The adversary answers `false` to every
query. If the tree stops after at most `m` queries on the all-false input, `m` unqueried positions
remain. The balanced input that is true on exactly those positions agrees with the all-false input
on every queried position, so it reaches the same leaf
(`Cslib.DecisionTree.eval_eq_of_forall_mem_queries`). But the two inputs need different answers.
de Wolf §2.4.1 states this bound with a one-line argument. Here it is derived for an arbitrary
tree, through the queries the tree makes on the all-false input.

**Upper bound.** Querying `m + 1` distinct positions suffices
(`Cslib.QueryComplexity.deutschJozsaTree_solves`). A balanced input cannot be constant on more
than `m` positions, so any `m + 1` positions of a balanced input contain both values.

So `m + 1` is the least decision-tree complexity of a total function that solves Deutsch–Jozsa
(`Cslib.QueryComplexity.isLeast_complexity_solvesDeutschJozsa`). For `N = 2^n` positions this is
`2^{n-1} + 1`, against the single exact quantum query of
`CslibFrontier/Computability/QueryComplexity/Quantum/DeutschJozsa.lean`.

## Main definitions

* `Cslib.QueryComplexity.SolvesDeutschJozsa`: a total function that answers the Deutsch–Jozsa
  promise problem.
* `Cslib.QueryComplexity.deutschJozsaTree`: query a list of positions and answer whether the bits
  read are all equal.

## Main results

* `Cslib.QueryComplexity.lt_depth_of_eval_ne`: over `2m` positions, a tree that separates the
  all-false input from every balanced input has depth greater than `m`.
* `Cslib.QueryComplexity.depth_ge_of_solvesDeutschJozsa`,
  `Cslib.QueryComplexity.complexity_ge_of_solvesDeutschJozsa`: the lower bound `m + 1`.
* `Cslib.QueryComplexity.deutschJozsaTree_solves`: `m + 1` distinct queries suffice.
* `Cslib.QueryComplexity.isLeast_complexity_solvesDeutschJozsa`: the deterministic complexity of
  the promise problem is exactly `m + 1`.

## References

* [D. Deutsch, R. Jozsa, *Rapid solution of problems by quantum computation*][DeutschJozsa1992]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §2.4.1
-/

public section

namespace Cslib.QueryComplexity

open Finset BitString

variable {ι : Type*} [Fintype ι]

/-- A total function `F` **solves the Deutsch–Jozsa problem** when it answers `true` on every
constant input and `false` on every balanced input. Inputs outside the promise are unconstrained. -/
structure SolvesDeutschJozsa (F : (ι → Bool) → Bool) : Prop where
  /-- `F` answers `true` on constant inputs. -/
  const : ∀ b, F (fun _ => b) = true
  /-- `F` answers `false` on balanced inputs. -/
  balanced : ∀ x, IsBalanced x → F x = false

/-- **The adversary bound.** Over `2m` positions, a decision tree that gives every balanced input
an output other than its output on the all-false input has depth greater than `m`. -/
theorem lt_depth_of_eval_ne {β : Type*} {m : ℕ} (hι : Fintype.card ι = 2 * m)
    (t : DecisionTree ι β) (ht : ∀ x, IsBalanced x → t.eval x ≠ t.eval fun _ => false) :
    m < t.depth := by
  classical
  by_contra hle
  push Not at hle
  set Q := t.queries fun _ => false
  have hQ : #Q ≤ m := (t.card_queries_le_depth _).trans hle
  have hQc : m ≤ #Qᶜ := by grind [card_compl]
  obtain ⟨T, hTQ, hT⟩ := exists_subset_card_eq hQc
  set y : ι → Bool := fun i => decide (i ∈ T)
  have hy : IsBalanced y := by
    rw [isBalanced_iff, hι, weight]
    simp only [y, decide_eq_true_eq, filter_mem_eq_inter, univ_inter, hT]
  refine ht y hy (t.eval_eq_of_forall_mem_queries fun i hi => ?_)
  have : i ∉ T := fun hiT => mem_compl.mp (hTQ hiT) hi
  simp [y, this]

/-- **The deterministic lower bound for Deutsch–Jozsa** [de Wolf, §2.4.1][deWolf2019]: over
`2m` positions, every decision tree that solves the Deutsch–Jozsa problem has depth at least
`m + 1`. -/
theorem depth_ge_of_solvesDeutschJozsa {m : ℕ} (hι : Fintype.card ι = 2 * m)
    (t : DecisionTree ι Bool) (ht : SolvesDeutschJozsa t.eval) : m + 1 ≤ t.depth :=
  lt_depth_of_eval_ne hι t fun x hx => by
    rw [ht.balanced x hx, ht.const false]
    exact Bool.false_ne_true

/-- **The deterministic query complexity of every total function solving Deutsch–Jozsa** over
`2m` positions is at least `m + 1`. -/
theorem complexity_ge_of_solvesDeutschJozsa {m : ℕ} (hι : Fintype.card ι = 2 * m)
    {F : (ι → Bool) → Bool} (hF : SolvesDeutschJozsa F) : m + 1 ≤ DecisionTree.complexity F := by
  obtain ⟨t, ht, hd⟩ := DecisionTree.exists_computes_depth_eq_complexity F
  rw [← hd]
  exact depth_ge_of_solvesDeutschJozsa hι t (DecisionTree.computes_iff.mp ht ▸ hF)

section Upper

variable [DecidableEq ι]

/-- Query the positions of `l` and answer whether the bits read are all equal. -/
def deutschJozsaTree (l : List ι) : DecisionTree ι Bool :=
  DecisionTree.queryAll (fun x => decide (∀ i ∈ l, ∀ j ∈ l, x i = x j)) l fun _ => false

/-- The tree `deutschJozsaTree l` answers whether `x` is constant on `l`. -/
theorem eval_deutschJozsaTree (l : List ι) (x : ι → Bool) :
    (deutschJozsaTree l).eval x = decide (∀ i ∈ l, ∀ j ∈ l, x i = x j) := by
  rw [deutschJozsaTree, DecisionTree.eval_queryAll]
  congr 1
  refine propext ⟨fun h i hi j hj => ?_, fun h i hi j hj => ?_⟩
  · simpa [hi, hj] using h i hi j hj
  · simpa [hi, hj] using h i hi j hj

theorem depth_deutschJozsaTree_le (l : List ι) : (deutschJozsaTree l).depth ≤ l.length :=
  DecisionTree.depth_queryAll_le _ _ _

/-- **`m + 1` distinct queries solve Deutsch–Jozsa** over `2m` positions: a balanced input is
constant on at most `m` positions. -/
theorem deutschJozsaTree_solves {m : ℕ} (hι : Fintype.card ι = 2 * m) {l : List ι}
    (hl : l.Nodup) (hlen : m < l.length) : SolvesDeutschJozsa (deutschJozsaTree l).eval := by
  refine ⟨fun b => by simp [eval_deutschJozsaTree], fun x hx => ?_⟩
  rw [eval_deutschJozsaTree, decide_eq_false_iff_not]
  intro h
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∈ l := List.exists_mem_of_length_pos (by omega)
  have hsub : l.toFinset ⊆ ({i | x i = x i₀} : Finset ι) := fun i hi =>
    mem_filter.mpr ⟨mem_univ i, h i (List.mem_toFinset.mp hi) i₀ hi₀⟩
  have hcard := card_le_card hsub
  rw [List.toFinset_card_of_nodup hl] at hcard
  have hbal := isBalanced_iff_card_filter.mp hx
  have hw : 2 * #{i | x i = true} = 2 * m := by
    rw [← hι]
    exact isBalanced_iff.mp hx
  cases hx₀ : x i₀ <;> rw [hx₀] at hcard <;> omega

end Upper

/-- `m + 1` distinct positions exist among `2m` positions when `m ≥ 1`. -/
theorem exists_nodup_length_eq {m : ℕ} (hι : Fintype.card ι = 2 * m) (hm : 0 < m) :
    ∃ l : List ι, l.Nodup ∧ l.length = m + 1 := by
  obtain ⟨T, -, hT⟩ := exists_subset_card_eq (s := (univ : Finset ι)) (n := m + 1)
    (by rw [card_univ]; omega)
  exact ⟨T.toList, T.nodup_toList, by rw [length_toList, hT]⟩

/-- **The deterministic query complexity of the Deutsch–Jozsa promise problem** over `2m ≥ 2`
positions is `m + 1`: it is the least decision-tree complexity of a total function that solves the
problem. -/
theorem isLeast_complexity_solvesDeutschJozsa {m : ℕ} (hι : Fintype.card ι = 2 * m) (hm : 0 < m) :
    IsLeast {d | ∃ F : (ι → Bool) → Bool, SolvesDeutschJozsa F ∧ DecisionTree.complexity F = d}
      (m + 1) := by
  classical
  refine ⟨?_, fun d ⟨F, hF, hd⟩ => hd ▸ complexity_ge_of_solvesDeutschJozsa hι hF⟩
  obtain ⟨l, hl, hlen⟩ := exists_nodup_length_eq hι hm
  have hsolves := deutschJozsaTree_solves hι hl (by omega)
  refine ⟨_, hsolves, le_antisymm ?_ (complexity_ge_of_solvesDeutschJozsa hι hsolves)⟩
  exact (DecisionTree.complexity_le_depth fun _ => rfl).trans
    ((depth_deutschJozsaTree_le l).trans hlen.le)

end Cslib.QueryComplexity
