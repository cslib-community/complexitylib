/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Dual
public import Complexity.Computability.DecisionTree.Evasive

/-!
# The AND–OR tree is evasive

The complete binary NAND tree of depth `d` (`QueryComplexity.nandTree d`) has `n = 2 ^ d` leaves,
addressed by their root-to-leaf paths `Fin d → Bool` (`false` for the left child). A leaf reads
its input bit, and an internal node outputs the NAND of its two children.

The complete binary AND–OR tree `T_{2,k}` of depth `2k` (`QueryComplexity.andOrTree k`) has
`n = 4 ^ k` leaves and alternating levels of gates, AND (MIN) at even distance from the root and OR
(MAX) at odd distance [Motwani and Raghavan, Section 2.1][MotwaniRaghavan95]. The OR–AND tree of
depth `2k` (`QueryComplexity.orAndTree k`), with OR at the root, is the NAND tree of depth `2k`,
since `NAND(NAND(a, b), NAND(c, d)) = (a ∧ b) ∨ (c ∧ d)` (`QueryComplexity.orAndTree_eq_nandTree`).
By De Morgan duality the AND–OR tree is the dual `x ↦ ¬ g(¬ x)` of the OR–AND tree `g`
(`QueryComplexity.andOrTree_eq_not_orAndTree`), so results transfer between the two orientations
through dual decision trees (`DecisionTree.dual`).

Every deterministic decision tree computing the NAND tree queries all `n` leaves on some input
(`QueryComplexity.exists_queries_eq_univ_of_computes_nandTree`), so `D = n`
(`QueryComplexity.complexity_nandTree`), and likewise for the AND–OR and OR–AND trees
(`QueryComplexity.exists_queries_eq_univ_of_computes_andOrTree`,
`QueryComplexity.complexity_andOrTree`). This follows from the parity criterion
(`DecisionTree.exists_queries_eq_univ_of_fourierCoeff_univ_ne_zero`): the sum over the inputs of
`(-1) ^ f(x) χ_{[n]}(x)` is `2` at every depth (`QueryComplexity.sum_signVal_nandTree_mul_chi`),
because splitting the input of a node into those of its two subtrees gives the recurrence
`s ↦ s² / 2`.

## Main definitions

* `Cslib.QueryComplexity.nandTree`: the complete binary NAND tree of depth `d`.
* `Cslib.QueryComplexity.andOrTree`: the complete binary AND–OR tree `T_{2,k}` of depth `2k`.
* `Cslib.QueryComplexity.orAndTree`: the complete binary OR–AND tree of depth `2k`.

## Main results

* `Cslib.QueryComplexity.orAndTree_eq_nandTree`: the OR–AND tree is the NAND tree of even depth.
* `Cslib.QueryComplexity.andOrTree_eq_not_orAndTree`: the AND–OR tree is the dual of the OR–AND
  tree.
* `Cslib.QueryComplexity.exists_queries_eq_univ_of_computes_andOrTree`: every decision tree
  computing the AND–OR tree queries all `4 ^ k` leaves on some input.
* `Cslib.QueryComplexity.complexity_andOrTree`: `D(T_{2,k}) = 4 ^ k`.

## References

* [R. Motwani, P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan95]
* [R. L. Rivest, J. Vuillemin, *On recognizing graph properties from adjacency
  matrices*][RivestVuillemin1976]
-/

public section

namespace Cslib.QueryComplexity

open BitString Finset

/-- The complete binary NAND tree of depth `d`, on the `2 ^ d` leaves addressed by root-to-leaf
paths (`false` for the left child): a leaf reads its bit, and a node is the NAND of its
children. -/
@[expose] def nandTree : (d : ℕ) → ((Fin d → Bool) → Bool) → Bool
  | 0, x => x Fin.elim0
  | d + 1, x => !(nandTree d (fun p => x (Fin.cons false p)) &&
      nandTree d (fun p => x (Fin.cons true p)))

/-- The complete binary AND–OR tree `T_{2,k}` of depth `2k`
[Motwani and Raghavan, Section 2.1][MotwaniRaghavan95]: an AND of two ORs at the root, each OR of
two copies of `T_{2,k-1}`, with leaves addressed by root-to-leaf paths. -/
@[expose] def andOrTree : (k : ℕ) → ((Fin (2 * k) → Bool) → Bool) → Bool
  | 0, x => x Fin.elim0
  | k + 1, x =>
    let sub (a b : Bool) := andOrTree k fun p => x (Fin.cons a (Fin.cons b p))
    (sub false false || sub false true) && (sub true false || sub true true)

/-- The complete binary OR–AND tree of depth `2k`: an OR of two ANDs at the root, each AND of two
copies of the OR–AND tree of depth `2k - 2`, with leaves addressed by root-to-leaf paths. -/
@[expose] def orAndTree : (k : ℕ) → ((Fin (2 * k) → Bool) → Bool) → Bool
  | 0, x => x Fin.elim0
  | k + 1, x =>
    let sub (a b : Bool) := orAndTree k fun p => x (Fin.cons a (Fin.cons b p))
    (sub false false && sub false true) || (sub true false && sub true true)

@[simp] theorem nandTree_zero (x : (Fin 0 → Bool) → Bool) : nandTree 0 x = x Fin.elim0 := rfl

theorem nandTree_succ (d : ℕ) (x : (Fin (d + 1) → Bool) → Bool) :
    nandTree (d + 1) x = !(nandTree d (fun p => x (Fin.cons false p)) &&
      nandTree d (fun p => x (Fin.cons true p))) := rfl

/-- The OR–AND tree of depth `2k` is the NAND tree of depth `2k`. -/
theorem orAndTree_eq_nandTree (k : ℕ) : orAndTree k = nandTree (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    change _ = nandTree (2 * k + 1 + 1) x
    simp only [orAndTree, ih, nandTree_succ]
    cases nandTree (2 * k) fun p => x (Fin.cons false (Fin.cons false p)) <;>
    cases nandTree (2 * k) fun p => x (Fin.cons false (Fin.cons true p)) <;>
    cases nandTree (2 * k) fun p => x (Fin.cons true (Fin.cons false p)) <;>
    cases nandTree (2 * k) fun p => x (Fin.cons true (Fin.cons true p)) <;> rfl

/-- **De Morgan duality**: the AND–OR tree is the dual of the OR–AND tree. -/
theorem andOrTree_eq_not_orAndTree (k : ℕ) (x : (Fin (2 * k) → Bool) → Bool) :
    andOrTree k x = !orAndTree k fun p => !x p := by
  induction k with
  | zero => simp [andOrTree, orAndTree]
  | succ k ih => simp only [andOrTree, orAndTree, ih, Bool.not_or, Bool.not_and]

/-- An input to the NAND tree of depth `d + 1` is a pair of inputs to its two subtrees of depth
`d`. -/
def splitInput (d : ℕ) : ((Fin (d + 1) → Bool) → Bool) ≃
    ((Fin d → Bool) → Bool) × ((Fin d → Bool) → Bool) where
  toFun x := (fun p => x (Fin.cons false p), fun p => x (Fin.cons true p))
  invFun yz q := cond (q 0) (yz.2 (Fin.tail q)) (yz.1 (Fin.tail q))
  left_inv x := by
    funext q
    rw [← Fin.cons_self_tail q]
    cases q 0 <;> simp
  right_inv yz := by
    ext p <;> simp

/-- The character of all leaves splits as the product of the characters of the leaves of the two
subtrees. -/
theorem chi_univ_eq_mul (d : ℕ) (x : (Fin (d + 1) → Bool) → Bool) :
    chi ℝ univ x = chi ℝ univ (fun p => x (Fin.cons false p)) *
      chi ℝ univ (fun p => x (Fin.cons true p)) := by
  simp only [chi_eq_prod_signVal]
  rw [← Fintype.prod_equiv (Fin.consEquiv fun _ => Bool)
    (fun bp => signVal (x (Fin.cons bp.1 bp.2))) _ fun _ => rfl, Fintype.prod_prod_type,
    Fintype.prod_bool, mul_comm]

private theorem signVal_not_and (a b : Bool) :
    signVal (!(a && b)) = (-1 - signVal a - signVal b + signVal a * signVal b) / 2 := by
  cases a <;> cases b <;> norm_num

/-- The top Fourier coefficient of the NAND tree, unnormalized: the sum over the inputs of
`(-1) ^ f(x) χ_{[n]}(x)` is `2` at every depth. -/
theorem sum_signVal_nandTree_mul_chi (d : ℕ) :
    ∑ x, signVal (nandTree d x) * chi ℝ univ x = 2 := by
  induction d with
  | zero =>
    have h (x : (Fin 0 → Bool) → Bool) : signVal (nandTree 0 x) * chi ℝ univ x = 1 := by
      rw [chi_eq_prod_signVal, Fintype.prod_unique, nandTree_zero]
      convert signVal_mul_self (x Fin.elim0)
    simp only [h, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_unique,
      pow_one, nsmul_eq_mul, mul_one]
    norm_num
  | succ d ih =>
    have hchi : ∑ y : (Fin d → Bool) → Bool, chi ℝ univ y = 0 := by
      rw [sum_chi, ite_eq_right univ_nonempty.ne_empty]
    rw [← (splitInput d).symm.sum_comp, Fintype.sum_prod_type]
    have h (y z : (Fin d → Bool) → Bool) :
        signVal (nandTree (d + 1) ((splitInput d).symm (y, z))) *
            chi ℝ univ ((splitInput d).symm (y, z)) =
          (-1 / 2) * (chi ℝ univ y * chi ℝ univ z) -
            (1 / 2) * ((signVal (nandTree d y) * chi ℝ univ y) * chi ℝ univ z) -
            (1 / 2) * (chi ℝ univ y * (signVal (nandTree d z) * chi ℝ univ z)) +
            (1 / 2) * ((signVal (nandTree d y) * chi ℝ univ y) *
              (signVal (nandTree d z) * chi ℝ univ z)) := by
      have h0 : (fun p => (splitInput d).symm (y, z) (Fin.cons false p)) = y :=
        funext fun p => by simp [splitInput]
      have h1 : (fun p => (splitInput d).symm (y, z) (Fin.cons true p)) = z :=
        funext fun p => by simp [splitInput]
      rw [nandTree_succ, chi_univ_eq_mul, h0, h1, signVal_not_and]
      ring
    simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hchi, ih]
    norm_num

/-- The top Fourier coefficient of the NAND tree, read as signs, is nonzero. -/
theorem fourierCoeff_nandTree_univ_ne_zero (d : ℕ) :
    fourierCoeff (fun x => signVal (nandTree d x)) univ ≠ 0 := by
  rw [fourierCoeff_eq_sum, sum_signVal_nandTree_mul_chi]
  positivity

/-- **The NAND tree is evasive**: every decision tree computing it queries all `2 ^ d` leaves on
some input. -/
theorem exists_queries_eq_univ_of_computes_nandTree {d : ℕ}
    {t : DecisionTree (Fin d → Bool) Bool} (ht : t.Computes (nandTree d)) :
    ∃ x, t.queries x = univ :=
  DecisionTree.exists_queries_eq_univ_of_fourierCoeff_univ_ne_zero
    (fourierCoeff_nandTree_univ_ne_zero d) ht

/-- `D = n` for the NAND tree on `n = 2 ^ d` leaves. -/
theorem complexity_nandTree (d : ℕ) : DecisionTree.complexity (nandTree d) = 2 ^ d := by
  rw [DecisionTree.complexity_eq_card_of_fourierCoeff_univ_ne_zero
    (fourierCoeff_nandTree_univ_ne_zero d), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]

/-- Every decision tree computing the OR–AND tree queries all `4 ^ k` leaves on some input. -/
theorem exists_queries_eq_univ_of_computes_orAndTree {k : ℕ}
    {t : DecisionTree (Fin (2 * k) → Bool) Bool} (ht : t.Computes (orAndTree k)) :
    ∃ x, t.queries x = univ :=
  exists_queries_eq_univ_of_computes_nandTree (orAndTree_eq_nandTree k ▸ ht)

/-- `D = 4 ^ k` for the OR–AND tree of depth `2k`. -/
theorem complexity_orAndTree (k : ℕ) : DecisionTree.complexity (orAndTree k) = 4 ^ k := by
  rw [orAndTree_eq_nandTree, complexity_nandTree, pow_mul]
  norm_num

/-- **The AND–OR tree is evasive** [Motwani and Raghavan, Section 2.1][MotwaniRaghavan95]: every
deterministic decision tree computing `T_{2,k}` queries all `4 ^ k` leaves on some input. -/
theorem exists_queries_eq_univ_of_computes_andOrTree {k : ℕ}
    {t : DecisionTree (Fin (2 * k) → Bool) Bool} (ht : t.Computes (andOrTree k)) :
    ∃ x, t.queries x = univ := by
  have hdual : t.dual.Computes (orAndTree k) := fun x => by
    rw [DecisionTree.eval_dual, ht, andOrTree_eq_not_orAndTree]
    simp only [Bool.not_not]
  obtain ⟨x, hx⟩ := exists_queries_eq_univ_of_computes_orAndTree hdual
  exact ⟨fun p => !x p, by rwa [DecisionTree.queries_dual] at hx⟩

/-- `D(T_{2,k}) = 4 ^ k`: the deterministic decision tree complexity of the AND–OR tree is its
number of leaves. -/
theorem complexity_andOrTree (k : ℕ) : DecisionTree.complexity (andOrTree k) = 4 ^ k := by
  rw [show andOrTree k = fun x => !orAndTree k fun p => !x p from
    funext (andOrTree_eq_not_orAndTree k), DecisionTree.complexity_dual, complexity_orAndTree]

end Cslib.QueryComplexity
