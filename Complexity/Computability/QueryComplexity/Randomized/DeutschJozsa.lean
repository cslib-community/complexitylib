/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.DeutschJozsa
public import Complexity.Computability.QueryComplexity.Randomized.ZeroError

/-!
# Randomized query algorithms for Deutsch–Jozsa

Deterministically, the Deutsch–Jozsa promise problem over `N = 2m` positions needs `m + 1`
queries (`Complexity/Computability/QueryComplexity/DeutschJozsa.lean`). With randomness and a
small error it needs only a constant number. [de Wolf, §2.4.1][deWolf2019] observes that querying
two random positions and answering "constant" exactly when the two bits agree is always correct
on constant inputs and correct with probability `1/2` on balanced inputs. So the quantum–classical
separation for this problem holds only for exact algorithms.

Here the randomized algorithm `Cslib.QueryComplexity.randomDeutschJozsa k` draws `k` positions
independently and uniformly, with replacement, queries them, and answers whether the bits read are
all equal. It makes at most `k` queries. It never errs on a constant input. On a balanced input it
errs exactly when all `k` positions fall among the `N/2` true positions or all among the `N/2` false
ones, which has probability `2 · (1/2)^k = 2/2^k` for `k ≥ 1`
(`Cslib.QueryComplexity.errorProb_randomDeutschJozsa_of_isBalanced`). For `k = 2` this is the
error `1/2` of de Wolf's remark. For `k = 3` the error `1/4` is below the usual bounded-error
threshold `1/3`, against `m + 1` deterministic queries
(`Cslib.QueryComplexity.randomDeutschJozsa_separation`).

The library's `Cslib.QueryComplexity.randomizedComplexity` asks for small error on *every* input,
while the Deutsch–Jozsa problem is a promise problem. So these bounds are stated for the error on
the promise inputs, as in the deterministic module.

## Main definitions

* `Cslib.QueryComplexity.randomDeutschJozsa`: query `k` random positions and answer whether the
  bits read are all equal.

## Main results

* `Cslib.QueryComplexity.depth_randomDeutschJozsa_le`: the algorithm makes at most `k` queries.
* `Cslib.QueryComplexity.errorProb_randomDeutschJozsa_const`: no error on constant inputs.
* `Cslib.QueryComplexity.errorProb_randomDeutschJozsa_of_isBalanced`: error exactly `2/2^k` on
  balanced inputs.
* `Cslib.QueryComplexity.randomDeutschJozsa_separation`: three random queries with error at most
  `1/4` on the promise, against `m + 1` deterministic queries.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §2.4.1
-/

public section

namespace Cslib.QueryComplexity

open Finset BitString RandomizedDecisionTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Query `k` positions drawn independently and uniformly at random, and answer whether the bits
read are all equal. -/
noncomputable def randomDeutschJozsa (k : ℕ) : RandomizedDecisionTree ι Bool :=
  uniformMixture fun l : Fin k → ι => deutschJozsaTree (List.ofFn l)

/-- The algorithm `randomDeutschJozsa k` makes at most `k` queries. -/
theorem depth_randomDeutschJozsa_le (k : ℕ) : (randomDeutschJozsa (ι := ι) k).depth ≤ k := by
  refine depth_le_iff.2 fun t ht => ?_
  obtain ⟨l, rfl⟩ := exists_eq_of_mem_support_uniformMixture ht
  exact (depth_deutschJozsaTree_le _).trans List.length_ofFn.le

/-- `randomDeutschJozsa k` never errs on a constant input. -/
theorem errorProb_randomDeutschJozsa_const (k : ℕ) {F : (ι → Bool) → Bool}
    (hF : SolvesDeutschJozsa F) (b : Bool) :
    (randomDeutschJozsa k).errorProb F (fun _ => b) = 0 :=
  errorProb_eq_zero_iff.2 fun t ht => by
    obtain ⟨l, rfl⟩ := exists_eq_of_mem_support_uniformMixture ht
    simp [eval_deutschJozsaTree, hF.const b]

omit [DecidableEq ι] [Nonempty ι] in
/-- For `k ≥ 1`, the bits of `x` at `k` positions are all equal exactly when the positions all lie
among the true positions of `x` or all among the false ones. -/
private theorem forall_mem_ofFn_eq_iff {k : ℕ} (hk : 0 < k) (x : ι → Bool) (l : Fin k → ι) :
    (∀ i ∈ List.ofFn l, ∀ j ∈ List.ofFn l, x i = x j) ↔
      (∀ a, l a ∈ ({i | x i = true} : Finset ι)) ∨
        ∀ a, l a ∈ ({i | x i = false} : Finset ι) := by
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, mem_filter, mem_univ,
    true_and]
  constructor
  · intro h
    cases h0 : x (l ⟨0, hk⟩)
    · exact Or.inr fun a => (h a ⟨0, hk⟩).trans h0
    · exact Or.inl fun a => (h a ⟨0, hk⟩).trans h0
  · rintro (h | h) a b <;> rw [h a, h b]

omit [Nonempty ι] in
/-- On a balanced input `x`, `2 · weight(x)^k` of the `(2 · weight(x))^k` position tuples read
bits that are all equal. -/
theorem card_filter_eval_deutschJozsaTree {k : ℕ} (hk : 0 < k) {x : ι → Bool}
    (hx : IsBalanced x) :
    #{l : Fin k → ι | (deutschJozsaTree (List.ofFn l)).eval x = true} = 2 * weight x ^ k := by
  have hset : ({l : Fin k → ι | (deutschJozsaTree (List.ofFn l)).eval x = true} : Finset _) =
      Fintype.piFinset (fun _ => ({i | x i = true} : Finset ι)) ∪
        Fintype.piFinset fun _ => ({i | x i = false} : Finset ι) := by
    ext l
    simp only [mem_filter, mem_univ, true_and, eval_deutschJozsaTree, decide_eq_true_eq,
      forall_mem_ofFn_eq_iff hk, mem_union, Fintype.mem_piFinset]
  rw [hset, card_union_of_disjoint, Fintype.card_piFinset, Fintype.card_piFinset, prod_const,
    prod_const, card_univ, Fintype.card_fin, isBalanced_iff_card_filter.mp hx, ← weight]
  · ring
  · rw [disjoint_left]
    intro l h1 h2
    have h1' := Fintype.mem_piFinset.1 h1 ⟨0, hk⟩
    have h2' := Fintype.mem_piFinset.1 h2 ⟨0, hk⟩
    simp_all

/-- **The error on balanced inputs**: for `k ≥ 1`, `randomDeutschJozsa k` errs on a balanced
input with probability exactly `2/2^k`. For `k = 2` this is the error `1/2` of
[de Wolf, §2.4.1][deWolf2019]. -/
theorem errorProb_randomDeutschJozsa_of_isBalanced {k : ℕ} (hk : 0 < k)
    {F : (ι → Bool) → Bool} (hF : SolvesDeutschJozsa F) {x : ι → Bool} (hx : IsBalanced x) :
    (randomDeutschJozsa k).errorProb F x = 2 / 2 ^ k := by
  have hw : (weight x : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := ι)
    have := isBalanced_iff.mp hx
    exact Nat.cast_ne_zero.2 (by omega)
  rw [randomDeutschJozsa, errorProb_uniformMixture, hF.balanced x hx]
  simp only [ne_eq, Bool.not_eq_false]
  rw [card_filter_eval_deutschJozsaTree hk hx, Fintype.card_fun, Fintype.card_fin,
    ← isBalanced_iff.mp hx]
  push_cast
  rw [mul_pow]
  field_simp

/-- **The error on the promise**: `randomDeutschJozsa k` errs with probability at most `2/2^k` on
every constant or balanced input. -/
theorem errorProb_randomDeutschJozsa_le (k : ℕ) {F : (ι → Bool) → Bool}
    (hF : SolvesDeutschJozsa F) {x : ι → Bool} (hx : (∃ c, x = fun _ => c) ∨ IsBalanced x) :
    (randomDeutschJozsa k).errorProb F x ≤ 2 / 2 ^ k := by
  rcases hx with ⟨c, rfl⟩ | hx
  · rw [errorProb_randomDeutschJozsa_const k hF c]
    positivity
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact errorProb_le_one.trans (by norm_num)
    · exact (errorProb_randomDeutschJozsa_of_isBalanced hk hF hx).le

/-- **Deutsch–Jozsa is easy with bounded error** [de Wolf, §2.4.1][deWolf2019]: over `N = 2m`
positions, three random queries solve the promise problem with error at most `1/4 < 1/3`, while
every deterministic decision tree needs `m + 1` queries. -/
theorem randomDeutschJozsa_separation {m : ℕ} (hι : Fintype.card ι = 2 * m) :
    (randomDeutschJozsa (ι := ι) 3).depth ≤ 3 ∧
      (∀ F : (ι → Bool) → Bool, SolvesDeutschJozsa F → ∀ x, (∃ c, x = fun _ => c) ∨
        IsBalanced x → (randomDeutschJozsa 3).errorProb F x ≤ 1 / 4) ∧
      ∀ F : (ι → Bool) → Bool, SolvesDeutschJozsa F → m + 1 ≤ DecisionTree.complexity F :=
  ⟨depth_randomDeutschJozsa_le 3, fun _ hF _ hx => (errorProb_randomDeutschJozsa_le 3 hF hx).trans
    (by norm_num), fun _ hF => complexity_ge_of_solvesDeutschJozsa hι hF⟩

end Cslib.QueryComplexity
