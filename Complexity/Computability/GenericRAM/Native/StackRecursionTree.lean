/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.StackRecursion
public import Complexity.Foundations.Data.Nat.RecursionTree

/-!
# Derivations of stack recursions from their recursion trees

A derivation `Cslib.GenericRAM.StackRecursion.Scheme.Eval` of a recursion scheme records the
value of a node with its number of nodes and its stack depth. This file builds derivations from
a description of the recursion tree, and reads off what a clocked run returns.

**Counted children** (`Scheme.Loop.counted`). A call whose accumulators `acc c` ask for the
children `child c` for `c < bound`, and then stop, runs its loop through the children's
derivations.

**The recursion tree** (`Scheme.exists_eval_of_counted`). Let `value` assign values to the nodes
satisfying `I.node`, such that a leaf has its leaf value, and a call at depth `d < D` has at most
`b d` counted children, all at depth `d + 1` and smaller in a measure, with its value the
`finish` of the accumulated children's values. Then every node at depth `d ≤ D` has a derivation
of its value, with at most `Nat.recursionBound b (D - d) d` nodes and at most `D - d` stack
levels. This is the induction "from the leaves" of a recursive algorithm, with its node count;
without the count, `Scheme.exists_eval_of_measure` is the induction alone.

**What a run returns** (`Scheme.value_of_run_eq_some`). Every value the clocked run returns, for
any fuel, satisfies the invariant of a derivation of the root. If the values carry a tag that
only the root's value has, a returned tagged value is the root's value, even when the fuel is too
small to vouch for the run.

## Main results

* `Cslib.GenericRAM.StackRecursion.Scheme.Loop.counted`: the loop over counted children.
* `Cslib.GenericRAM.StackRecursion.Scheme.exists_eval_of_measure`: derivations by well-founded
  recursion.
* `Cslib.GenericRAM.StackRecursion.Scheme.exists_eval_of_counted`: derivations with the node count
  of the recursion tree.
* `Cslib.GenericRAM.StackRecursion.Scheme.value_of_run_eq_some`: a returned value satisfies the
  invariant.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.GenericRAM.StackRecursion.Scheme

open Finset

variable {X A Y : Type} {R : Scheme X A Y} {I : Invariant X A Y}

/-- **A call with counted children.** If, from the accumulators `acc c`, the call `x` asks for the
children `child c` for `c < bound` and then stops, and the children evaluate to `val c`, then its
loop from `acc 0` ends at `acc bound`, with the children's nodes and at most `H` levels. -/
theorem Loop.counted {x : X} {acc : ℕ → A} {child : ℕ → X} {val : ℕ → Y} {nodes height : ℕ → ℕ}
    (bound H : ℕ) (hnext : ∀ c < bound, R.next x (acc c) = some (child c))
    (hdone : R.next x (acc bound) = none)
    (habsorb : ∀ c < bound, R.absorb x (acc c) (val c) = acc (c + 1))
    (heval : ∀ c < bound, R.Eval I (child c) (val c) (nodes c) (height c))
    (hframe : ∀ c < bound, I.frame x (acc c)) (hH : ∀ c < bound, height c ≤ H) :
    ∃ h ≤ H, R.Loop I x (acc 0) (acc bound) (∑ c ∈ range bound, nodes c) h := by
  -- From any start `s ≤ bound`.
  have key : ∀ k s, s + k = bound →
      ∃ h ≤ H, R.Loop I x (acc s) (acc bound) (∑ c ∈ Ico s bound, nodes c) h := by
    intro k
    induction k with
    | zero =>
      intro s hs
      subst hs
      exact ⟨0, Nat.zero_le _, by simpa using Loop.done hdone⟩
    | succ k ih =>
      intro s hs
      obtain ⟨h, hh, hl⟩ := ih (s + 1) (by omega)
      have hs' : s < bound := by omega
      have hl' := Loop.child (hframe s hs') (hnext s hs') (heval s hs')
        (by rw [habsorb s hs']; exact hl)
      refine ⟨max (height s) h, max_le (hH s hs') hh, ?_⟩
      rwa [sum_eq_sum_Ico_succ_bot hs']
  simpa using key bound 0 (by omega)

/-- **Derivations by well-founded recursion.** Let `value` assign values to the nodes satisfying
`I.node`, all satisfying `I.value`, such that a leaf has its leaf value, and a call has counted
children: from the accumulators `acc c`, starting at `start`, it asks for `child c` for `c < cnt`
and then stops, absorbing the children's values; the frames satisfy `I.frame`, the children
satisfy `I.node` and are smaller in the measure `μ`; and its value is the `finish` of the last
accumulator. Then every node has a derivation of its value. `exists_eval_of_counted` adds the node
count. -/
theorem exists_eval_of_measure (μ : X → ℕ) (value : X → Y)
    (hleaf : ∀ x, I.node x → R.isLeaf x = true → value x = R.leaf x)
    (hcall : ∀ x, I.node x → R.isLeaf x = false →
      ∃ (cnt : ℕ) (acc : ℕ → A) (child : ℕ → X), acc 0 = R.start x ∧
        (∀ c < cnt, R.next x (acc c) = some (child c)) ∧ R.next x (acc cnt) = none ∧
        (∀ c < cnt, R.absorb x (acc c) (value (child c)) = acc (c + 1)) ∧
        (∀ c < cnt, I.frame x (acc c) ∧ I.node (child c) ∧ μ (child c) < μ x) ∧
        value x = R.finish x (acc cnt))
    (hvalue : ∀ x, I.node x → I.value (value x)) (x : X) (hx : I.node x) :
    ∃ n h, R.Eval I x (value x) n h := by
  induction hμ : μ x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
  cases hl : R.isLeaf x
  · obtain ⟨cnt, acc, child, h0, hnext, hdone, habs, hkids, hfin⟩ := hcall x hx hl
    have hev : ∀ c < cnt, ∃ n h, R.Eval I (child c) (value (child c)) n h := fun c hc =>
      ih (μ (child c)) (hμ ▸ (hkids c hc).2.2) (child c) (hkids c hc).2.1 rfl
    choose! nodes height hev using hev
    obtain ⟨h, -, hloop⟩ := Loop.counted (I := I) (val := fun c => value (child c)) cnt
      (∑ c ∈ range cnt, height c) hnext hdone habs hev (fun c hc => (hkids c hc).1)
      (fun c hc => single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr hc))
    rw [h0] at hloop
    exact ⟨_, _, hfin ▸ Eval.call hx hl hloop (hfin ▸ hvalue x hx)⟩
  · exact ⟨1, 0, by rw [hleaf x hx hl]; exact Eval.leaf hx hl (hleaf x hx hl ▸ hvalue x hx)⟩

/-- A recursion tree has at least its root. -/
private theorem one_le_recursionBound (b : ℕ → ℕ) (k d : ℕ) : 1 ≤ Nat.recursionBound b k d := by
  cases k with
  | zero => simp
  | succ k => rw [Nat.recursionBound_succ]; omega

/-- **Derivations from the recursion tree.** Let `value` assign values to the nodes satisfying
`I.node`, all satisfying `I.value`, such that

* a leaf has its leaf value;
* a call at depth `d` has `d < D` and at most `b d` children, counted: from the accumulators
  `acc c`, starting at `start`, it asks for `child c` for `c < cnt` and then stops, absorbing the
  children's values; the frames satisfy `I.frame`, and the children satisfy `I.node`, are smaller
  in the measure `μ` and lie at depth `d + 1`; and its value is the `finish` of the last
  accumulator.

Then every node at depth `d ≤ D` has a derivation of its value with at most
`Nat.recursionBound b (D - d) d` nodes and at most `D - d` stack levels. -/
theorem exists_eval_of_counted (μ depth : X → ℕ) (value : X → Y) (b : ℕ → ℕ) (D : ℕ)
    (hleaf : ∀ x, I.node x → R.isLeaf x = true → value x = R.leaf x)
    (hcall : ∀ x, I.node x → R.isLeaf x = false → depth x < D ∧
      ∃ (cnt : ℕ) (acc : ℕ → A) (child : ℕ → X), cnt ≤ b (depth x) ∧ acc 0 = R.start x ∧
        (∀ c < cnt, R.next x (acc c) = some (child c)) ∧ R.next x (acc cnt) = none ∧
        (∀ c < cnt, R.absorb x (acc c) (value (child c)) = acc (c + 1)) ∧
        (∀ c < cnt, I.frame x (acc c) ∧ I.node (child c) ∧ μ (child c) < μ x ∧
          depth (child c) = depth x + 1) ∧
        value x = R.finish x (acc cnt))
    (hvalue : ∀ x, I.node x → I.value (value x)) (x : X) (hx : I.node x) (hxD : depth x ≤ D) :
    ∃ n h, R.Eval I x (value x) n h ∧ n ≤ Nat.recursionBound b (D - depth x) (depth x) ∧
      h ≤ D - depth x := by
  induction hμ : μ x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
  cases hl : R.isLeaf x
  · obtain ⟨hd, cnt, acc, child, hcnt, h0, hnext, hdone, habs, hkids, hfin⟩ := hcall x hx hl
    have hev : ∀ c < cnt, ∃ n h, R.Eval I (child c) (value (child c)) n h ∧
        n ≤ Nat.recursionBound b (D - (depth x + 1)) (depth x + 1) ∧
        h ≤ D - (depth x + 1) := fun c hc => by
      obtain ⟨-, hn, hμc, hdc⟩ := hkids c hc
      obtain ⟨n, h, he, hnb, hhb⟩ := ih (μ (child c)) (hμ ▸ hμc) (child c) hn (by omega) rfl
      rw [hdc] at hnb hhb
      exact ⟨n, h, he, hnb, hhb⟩
    choose! nodes height hev using hev
    obtain ⟨h, hh, hloop⟩ := Loop.counted (I := I) (val := fun c => value (child c)) cnt
      (D - (depth x + 1)) hnext hdone habs (fun c hc => (hev c hc).1)
      (fun c hc => (hkids c hc).1) (fun c hc => (hev c hc).2.2)
    rw [h0] at hloop
    have hv : I.value (R.finish x (acc cnt)) := hfin ▸ hvalue x hx
    refine ⟨(∑ c ∈ range cnt, nodes c) + 1, h + 1, hfin ▸ Eval.call hx hl hloop hv, ?_, by omega⟩
    obtain ⟨k', hk'⟩ : ∃ k', D - depth x = k' + 1 := ⟨D - depth x - 1, by omega⟩
    have hk'' : D - (depth x + 1) = k' := by omega
    rw [hk', Nat.recursionBound_succ]
    have hsum : ∑ c ∈ range cnt, nodes c ≤ cnt * Nat.recursionBound b k' (depth x + 1) := by
      calc ∑ c ∈ range cnt, nodes c ≤ ∑ _c ∈ range cnt, Nat.recursionBound b k' (depth x + 1) :=
            sum_le_sum fun c hc => hk'' ▸ (hev c (mem_range.mp hc)).2.1
        _ = cnt * Nat.recursionBound b k' (depth x + 1) := by rw [sum_const, card_range,
            smul_eq_mul]
    have := Nat.mul_le_mul_right (Nat.recursionBound b k' (depth x + 1)) hcnt
    omega
  · refine ⟨1, 0, ?_, one_le_recursionBound _ _ _, Nat.zero_le _⟩
    rw [hleaf x hx hl]
    exact Eval.leaf hx hl (hleaf x hx hl ▸ hvalue x hx)

/-- **What a clocked run returns.** For any fuel, a value returned by the run satisfies the
invariant of a derivation of the root. -/
theorem value_of_run_eq_some {J : Type} {fuel : J → ℕ} {root : J → X} {a : J} {y y' : Y}
    {N H : ℕ} (he : R.Eval I (root a) y N H) (hrun : R.run fuel root a = some y') :
    I.value y' := by
  obtain ⟨-, -, ⟨x, hr, -⟩ | ⟨z, hr, hz⟩⟩ := he.good_iterate (fuel a)
  · simp only [run] at hrun
    rw [hr] at hrun
    simp at hrun
  · simp only [run] at hrun
    rw [hr] at hrun
    cases hrun
    exact hz

end Cslib.GenericRAM.StackRecursion.Scheme
