/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Tree
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Sparsification -- explicit thresholds and the leaf count

For a width `k ≥ 1` and a parameter `α ≥ 1`, let `X = 2 k α` and take the thresholds
`θ 0 = 1`, `θ j = α X ^ (2 j - 1)` (`threshold`). Then along every branch from a clause set whose
variables are among `N` given ones, ending in a sparse node, at most `N X ^ (2 c - 1)` clauses of
size `c` are introduced (`Path.card_introducedOfCard_le_pow`), by induction on `c` from the
recursive bound of the path analysis: the products `θ (c - h) · X ^ (2 h - 1)` all equal
`α X ^ (2 c - 2)`, and `2 α c ≤ X`. Hence every branch has length at most `Λ = N k X ^ (2 k)`, at
most `(k - 1) N / α` petal steps, and nodes with at most `Λ` more clauses than the root.

For any branching rule, a leaf word is determined by the positions of its petal steps among the
first `Λ` steps (`BranchingRule.IsLeafWord.eq_of_getD_eq`), so there are at most
`∑_{j ≤ (k - 1) N / α} (Λ choose j)` leaf words (`BranchingRule.card_le_of_isLeafWord`), and the
canonical rule gives a family of that many leaves (`exists_leaves`). The leaves are sparse, so
every variable occurs in at most `2 ∑_{c < k} θ c` of their clauses (`occurrences_le_of_sparse`),
and they have at most `2 (∑_{c < k} θ c) N + 1` clauses (`card_le_of_sparse`).

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.base`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.threshold`: the threshold base `X = 2 k α` and the
  explicit thresholds.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.Path.len_le`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Path.mul_card_petal_le`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Path.card_node_le`: branches are short, have few petal
  steps and small nodes.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.card_le_of_isLeafWord`: the number of
  leaves of any branching rule.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.IsNodeWord.card_walk_le`: the states of
  the tree are small.
* `Cslib.Logic.PL.ClauseSet.Sparsification.exists_leaves`: the leaves of the canonical rule.
* `Cslib.Logic.PL.ClauseSet.Sparsification.occurrences_le_of_sparse`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.card_le_of_sparse`: sparse clause sets are sparse.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
* [C. Calabro, *The Exponential Complexity of Satisfiability Problems*][Calabro2009]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- The base `X = 2 k α` of the thresholds. -/
def base (k α : ℕ) : ℕ := 2 * k * α

/-- The thresholds: `θ 0 = 1` and `θ j = α X ^ (2 j - 1)` for `j ≥ 1`. -/
def threshold (k α j : ℕ) : ℕ := if j = 0 then 1 else α * base k α ^ (2 * j - 1)

variable {k α : ℕ}

/-- When `1 ≤ k` and `1 ≤ α`, the threshold base `base k α` is at least `1`. -/
theorem one_le_base (hk : 1 ≤ k) (hα : 1 ≤ α) : 1 ≤ base k α := by
  unfold base
  have : 1 ≤ k * α := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  nlinarith

/-- When `1 ≤ k` and `1 ≤ α`, every threshold `threshold k α j` is at least `1`. -/
theorem one_le_threshold (hk : 1 ≤ k) (hα : 1 ≤ α) (j : ℕ) : 1 ≤ threshold k α j := by
  unfold threshold
  split_ifs
  · exact le_rfl
  · exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by have := one_le_base hk hα; omega)))

/-- For `1 ≤ j`, `threshold k α j` equals `α * base k α ^ (2 * j - 1)`. -/
theorem threshold_of_one_le {j : ℕ} (hj : 1 ≤ j) :
    threshold k α j = α * base k α ^ (2 * j - 1) := by
  unfold threshold
  rw [ite_eq_right (by omega)]

private theorem threshold_pred_le (hk : 1 ≤ k) (hα : 1 ≤ α) {c : ℕ} (hc : 1 ≤ c) :
    threshold k α (c - 1) ≤ α * base k α ^ (2 * c - 2) := by
  rcases Nat.eq_or_lt_of_le hc with rfl | hc2
  · simp [threshold, hα]
  · rw [threshold_of_one_le (by omega)]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_base hk hα) (by omega))

namespace Path

variable (hk : 1 ≤ k) (hα : 1 ≤ α)
include hk hα

/-- **Introduced clauses of each size.** Along a branch from a clause set of width `k` over the
`N` variables of `U`, ending in a sparse node, at most `N X ^ (2 c - 1)` clauses of size `c` are
introduced, for `1 ≤ c ≤ k`. -/
theorem card_introducedOfCard_le_pow (P : Path (threshold k α) V)
    (hleaf : Sparse (threshold k α) (P.node P.len)) (U : Finset V)
    (hU : ∀ C ∈ P.node 0, ∀ l ∈ C, l.1 ∈ U) :
    ∀ c, 1 ≤ c → c ≤ k → (P.introducedOfCard c).card ≤ U.card * base k α ^ (2 * c - 1) := by
  have hθ := one_le_threshold hk hα
  set X := base k α
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc hck
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hrec := P.card_introducedOfCard_le hθ hleaf U hU hc
    have hterm : ∀ h ∈ Ico 1 (c' + 1),
        2 * threshold k α (c' + 1 - h) * (P.introducedOfCard h).card ≤
          2 * α * U.card * X ^ (2 * c') := by
      intro h hh
      obtain ⟨hh1, hhc⟩ := mem_Ico.mp hh
      rw [threshold_of_one_le (by omega)]
      have hIh := ih h hhc hh1 (by omega)
      calc 2 * (α * X ^ (2 * (c' + 1 - h) - 1)) * (P.introducedOfCard h).card
          ≤ 2 * (α * X ^ (2 * (c' + 1 - h) - 1)) * (U.card * X ^ (2 * h - 1)) :=
            Nat.mul_le_mul_left _ hIh
        _ = 2 * α * U.card * X ^ ((2 * (c' + 1 - h) - 1) + (2 * h - 1)) := by
          rw [pow_add]; ring
        _ = 2 * α * U.card * X ^ (2 * c') := by congr 2; omega
    calc (P.introducedOfCard (c' + 1)).card
        ≤ 2 * U.card * threshold k α (c' + 1 - 1) +
            ∑ h ∈ Ico 1 (c' + 1), 2 * threshold k α (c' + 1 - h) *
              (P.introducedOfCard h).card := hrec
      _ ≤ 2 * U.card * (α * X ^ (2 * (c' + 1) - 2)) +
          ∑ _h ∈ Ico 1 (c' + 1), 2 * α * U.card * X ^ (2 * c') :=
          add_le_add (Nat.mul_le_mul_left _ (threshold_pred_le hk hα hc)) (sum_le_sum hterm)
      _ = (c' + 1) * (2 * α * U.card * X ^ (2 * c')) := by
          rw [sum_const, Nat.card_Ico, smul_eq_mul, Nat.add_sub_cancel,
            show 2 * (c' + 1) - 2 = 2 * c' by omega]
          ring
      _ ≤ k * (2 * α * U.card * X ^ (2 * c')) := Nat.mul_le_mul_right _ hck
      _ = U.card * X ^ (2 * (c' + 1) - 1) := by
          rw [show 2 * (c' + 1) - 1 = 2 * c' + 1 by omega, pow_succ]
          simp only [X, base]
          ring

/-- **Few introduced clauses.** Along a branch from a clause set of width `k` over the `N`
variables of `U`, ending in a sparse node, at most `N k X ^ (2 k)` clauses are introduced. -/
private theorem card_introduced_le (P : Path (threshold k α) V) (hk0 : ∀ C ∈ P.node 0, C.card ≤ k)
    (hleaf : Sparse (threshold k α) (P.node P.len)) (U : Finset V)
    (hU : ∀ C ∈ P.node 0, ∀ l ∈ C, l.1 ∈ U) :
    P.introduced.card ≤ U.card * (k * base k α ^ (2 * k)) := by
  have hθ := one_le_threshold hk hα
  calc P.introduced.card = ∑ c ∈ Ico 1 k, (P.introducedOfCard c).card :=
        P.card_introduced_eq_sum hθ hk0
    _ ≤ ∑ _c ∈ Ico 1 k, U.card * base k α ^ (2 * k) := by
        refine sum_le_sum fun c hc => ?_
        obtain ⟨hc1, hck⟩ := mem_Ico.mp hc
        refine (card_introducedOfCard_le_pow hk hα P hleaf U hU c hc1 hck.le).trans ?_
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_base hk hα) (by omega))
    _ ≤ U.card * (k * base k α ^ (2 * k)) := by
        rw [sum_const, Nat.card_Ico, smul_eq_mul]
        calc (k - 1) * (U.card * base k α ^ (2 * k))
            ≤ k * (U.card * base k α ^ (2 * k)) := Nat.mul_le_mul_right _ (Nat.sub_le k 1)
          _ = U.card * (k * base k α ^ (2 * k)) := by ring

/-- **Branches are short.** A branch from a clause set of width `k` over the `N` variables of `U`,
ending in a sparse node, has at most `N k X ^ (2 k)` steps. -/
theorem len_le (P : Path (threshold k α) V) (hk0 : ∀ C ∈ P.node 0, C.card ≤ k)
    (hleaf : Sparse (threshold k α) (P.node P.len)) (U : Finset V)
    (hU : ∀ C ∈ P.node 0, ∀ l ∈ C, l.1 ∈ U) :
    P.len ≤ U.card * (k * base k α ^ (2 * k)) :=
  (P.len_le_card_introduced (one_le_threshold hk hα)).trans
    (card_introduced_le hk hα P hk0 hleaf U hU)

/-- **Nodes are small.** Every node of a branch from a clause set `ψ` of width `k` over the `N`
variables of `U`, ending in a sparse node, has at most `|ψ| + N k X ^ (2 k)` clauses. -/
theorem card_node_le (P : Path (threshold k α) V) (hk0 : ∀ C ∈ P.node 0, C.card ≤ k)
    (hleaf : Sparse (threshold k α) (P.node P.len)) (U : Finset V)
    (hU : ∀ C ∈ P.node 0, ∀ l ∈ C, l.1 ∈ U) {i : ℕ} (hi : i ≤ P.len) :
    (P.node i).card ≤ (P.node 0).card + U.card * (k * base k α ^ (2 * k)) := by
  have hθ := one_le_threshold hk hα
  have hsub : ∀ i ≤ P.len, P.node i ⊆ P.node 0 ∪ P.introduced := by
    intro i hi
    induction i with
    | zero => exact subset_union_left
    | succ i ih =>
      refine (P.node_succ_subset (by omega)).trans (union_subset (ih (by omega)) ?_)
      exact (subset_biUnion_of_mem P.introAt (mem_range.mpr (by omega))).trans
        subset_union_right
  calc (P.node i).card ≤ (P.node 0 ∪ P.introduced).card := card_le_card (hsub i hi)
    _ ≤ (P.node 0).card + P.introduced.card := card_union_le _ _
    _ ≤ (P.node 0).card + U.card * (k * base k α ^ (2 * k)) :=
        Nat.add_le_add_left (card_introduced_le hk hα P hk0 hleaf U hU) _

/-- **Few petal steps.** A branch from a clause set of width `k` over the `N` variables of `U`,
ending in a sparse node, has at most `(k - 1) N / α` petal steps. -/
theorem mul_card_petal_le (P : Path (threshold k α) V) (hk0 : ∀ C ∈ P.node 0, C.card ≤ k)
    (hleaf : Sparse (threshold k α) (P.node P.len)) (U : Finset V)
    (hU : ∀ C ∈ P.node 0, ∀ l ∈ C, l.1 ∈ U) :
    α * ((range P.len).filter fun i => P.dir i = true).card ≤ (k - 1) * U.card := by
  have hθ := one_le_threshold hk hα
  have hj : ∀ j ∈ Ico 1 k, α * (P.petalSteps j).card ≤ U.card := by
    intro j hj
    obtain ⟨hj1, hjk⟩ := mem_Ico.mp hj
    have h1 := P.mul_card_petalSteps_le hθ j
    have h2 := card_introducedOfCard_le_pow hk hα P hleaf U hU j hj1 hjk.le
    rw [threshold_of_one_le hj1] at h1
    have hpos : 0 < base k α ^ (2 * j - 1) := pow_pos (one_le_base hk hα) _
    have : α * (P.petalSteps j).card * base k α ^ (2 * j - 1) ≤
        U.card * base k α ^ (2 * j - 1) := by
      calc α * (P.petalSteps j).card * base k α ^ (2 * j - 1)
          = α * base k α ^ (2 * j - 1) * (P.petalSteps j).card := by ring
        _ ≤ U.card * base k α ^ (2 * j - 1) := h1.trans h2
    exact Nat.le_of_mul_le_mul_right this hpos
  calc α * ((range P.len).filter fun i => P.dir i = true).card
      ≤ α * ∑ j ∈ Ico 1 k, (P.petalSteps j).card :=
        Nat.mul_le_mul_left _ (P.card_petal_le_sum hθ hk0)
    _ = ∑ j ∈ Ico 1 k, α * (P.petalSteps j).card := mul_sum _ _ _
    _ ≤ ∑ _j ∈ Ico 1 k, U.card := sum_le_sum hj
    _ = (k - 1) * U.card := by rw [sum_const, Nat.card_Ico, smul_eq_mul]

end Path

/-! ### The leaves of a branching rule -/

namespace BranchingRule

variable {σ : Type*} {R : BranchingRule (threshold k α) V σ} {s : σ}

section

variable (hk : 1 ≤ k) (hα : 1 ≤ α) (hred : Reduced (R.toClauseSet s))
  (hk0 : ∀ C ∈ R.toClauseSet s, C.card ≤ k) (U : Finset V)
  (hU : ∀ C ∈ R.toClauseSet s, ∀ l ∈ C, l.1 ∈ U)
include hk hα hred hk0 hU

/-- **Leaf words are short.** From a reduced clause set of width `k` over the `N` variables of `U`,
every leaf word has length at most `N k X ^ (2 k)`. -/
theorem IsLeafWord.length_le {w : List Bool} (hw : R.IsLeafWord s w) :
    w.length ≤ U.card * (k * base k α ^ (2 * k)) := by
  obtain ⟨P, hP0, hPlen, hPleaf, -⟩ := exists_path_of_isLeafWord hred hw
  have h0 : P.node 0 = R.toClauseSet s := by simpa [walk] using hP0 0 (Nat.zero_le _)
  rw [← hPlen]
  exact Path.len_le hk hα P (h0 ▸ hk0) hPleaf U (h0 ▸ hU)

/-- **Leaf words have few petal steps.** From a reduced clause set of width `k` over the `N`
variables of `U`, every leaf word has at most `(k - 1) N / α` petal steps. -/
private theorem IsLeafWord.mul_card_le {w : List Bool} (hw : R.IsLeafWord s w) :
    α * ((range w.length).filter fun i => w.getD i false = true).card ≤ (k - 1) * U.card := by
  obtain ⟨P, hP0, hPlen, hPleaf, hPdir⟩ := exists_path_of_isLeafWord hred hw
  have h0 : P.node 0 = R.toClauseSet s := by simpa [walk] using hP0 0 (Nat.zero_le _)
  rw [← hPdir]
  exact Path.mul_card_petal_le hk hα P (h0 ▸ hk0) hPleaf U (h0 ▸ hU)

/-- **Few leaves.** From a reduced clause set of width `k` over the `N` variables of `U`, there
are at most `∑_{j ≤ (k - 1) N / α} (Λ choose j)` leaf words, `Λ = N k X ^ (2 k)`. -/
theorem card_le_of_isLeafWord (W : Finset (List Bool)) (hW : ∀ w ∈ W, R.IsLeafWord s w) :
    W.card ≤ ∑ j ∈ range ((k - 1) * U.card / α + 1),
      (U.card * (k * base k α ^ (2 * k))).choose j := by
  classical
  set Λ := U.card * (k * base k α ^ (2 * k))
  set ρ := (k - 1) * U.card / α
  let pos (w : List Bool) : Finset ℕ := (range Λ).filter fun i => w.getD i false = true
  have hpos : ∀ w ∈ W, pos w ∈ (range Λ).powerset.filter (·.card ≤ ρ) := by
    intro w hw
    have hlen := (hW w hw).length_le hk hα hred hk0 U hU
    refine mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), ?_⟩
    refine (Nat.le_div_iff_mul_le (by omega)).mpr ((Nat.mul_comm _ _).trans_le
      ((Nat.mul_le_mul_left α (card_le_card fun i hi => ?_)).trans
        ((hW w hw).mul_card_le hk hα hred hk0 U hU)))
    obtain ⟨-, hi⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨mem_range.mpr ?_, hi⟩
    by_contra hge
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.false_ne_true hi
  have hinj : Set.InjOn pos W := by
    intro w hw w' hw' h
    refine (hW w hw).eq_of_getD_eq (hW w' hw') fun i => ?_
    by_cases hi : i < Λ
    · have := congrArg (i ∈ ·) h
      simp only [pos, mem_filter, mem_range, hi, true_and, eq_iff_iff] at this
      cases hwi : w.getD i false <;> cases hw'i : w'.getD i false <;> simp_all
    · have hl := (hW w hw).length_le hk hα hred hk0 U hU
      have hl' := (hW w' hw').length_le hk hα hred hk0 U hU
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  calc W.card = (W.image pos).card := (card_image_of_injOn hinj).symm
    _ ≤ ((range Λ).powerset.filter (·.card ≤ ρ)).card :=
        card_le_card fun t ht => by
          obtain ⟨w, hw, rfl⟩ := mem_image.mp ht
          exact hpos w hw
    _ ≤ ((range (ρ + 1)).biUnion fun j => (range Λ).powersetCard j).card := by
        refine card_le_card fun t ht => ?_
        obtain ⟨htΛ, htρ⟩ := mem_filter.mp ht
        exact mem_biUnion.mpr ⟨t.card, mem_range.mpr (by omega),
          mem_powersetCard.mpr ⟨mem_powerset.mp htΛ, rfl⟩⟩
    _ ≤ ∑ j ∈ range (ρ + 1), ((range Λ).powersetCard j).card := card_biUnion_le
    _ = ∑ j ∈ range (ρ + 1), Λ.choose j := by
        refine sum_congr rfl fun j _ => ?_
        rw [card_powersetCard, card_range]

/-- **The states of the tree are small.** From a reduced clause set `ψ` of width `k` over the `N`
variables of `U`, every state reached along a node word has at most `|ψ| + N k X ^ (2 k)`
clauses. -/
theorem IsNodeWord.card_walk_le {w : List Bool} (hw : R.IsNodeWord s w) :
    (R.toClauseSet (R.walk s w)).card ≤
      (R.toClauseSet s).card + U.card * (k * base k α ^ (2 * k)) := by
  obtain ⟨u, hu⟩ := hw.exists_isLeafWord_append (one_le_threshold hk hα)
  obtain ⟨P, hP0, hPlen, hPleaf, -⟩ := exists_path_of_isLeafWord hred hu
  have h0 : P.node 0 = R.toClauseSet s := by simpa [walk] using hP0 0 (Nat.zero_le _)
  have hw' : P.node w.length = R.toClauseSet (R.walk s w) := by
    rw [hP0 _ (by simp), List.take_left]
  rw [← hw', ← h0]
  exact Path.card_node_le hk hα P (h0 ▸ hk0) hPleaf U (h0 ▸ hU) (by rw [hPlen]; simp)

end

end BranchingRule

/-- **The leaves.** For width `k ≥ 1` and `α ≥ 1`, every clause set `φ` of width `k` has a family
of at most `∑_{j ≤ (k - 1) N / α} (Λ choose j)` sparse clause sets, `Λ = N k X ^ (2 k)`, each
refining `φ` and having only solutions of `φ`, whose solutions cover those of `φ`. -/
theorem exists_leaves [Fintype V] (hk : 1 ≤ k) (hα : 1 ≤ α) (φ : ClauseSet V)
    (hφ : ∀ C ∈ φ, C.card ≤ k) :
    ∃ Ψ : Finset (ClauseSet V),
      Ψ.card ≤ ∑ j ∈ range ((k - 1) * Fintype.card V / α + 1),
        (Fintype.card V * (k * base k α ^ (2 * k))).choose j ∧
      (∀ ψ ∈ Ψ, Sparse (threshold k α) ψ ∧ Refines ψ φ ∧
        ∀ x, ψ.Sat x → φ.Sat x) ∧
      ∀ x, φ.Sat x → ∃ ψ ∈ Ψ, ψ.Sat x := by
  classical
  have hθ := one_le_threshold hk hα
  set θ := threshold k α
  set R : BranchingRule θ V (ClauseSet V) := chooseRule θ
  set Λ := Fintype.card V * (k * base k α ^ (2 * k))
  set ρ := (k - 1) * Fintype.card V / α
  set ψ₀ := reduce φ
  have hψ₀ : ∀ C ∈ ψ₀, C.card ≤ k := fun C hC => hφ C (reduce_subset φ hC)
  have hU : ∀ C ∈ R.toClauseSet ψ₀, ∀ l ∈ C, l.1 ∈ (univ : Finset V) :=
    fun _ _ _ _ => mem_univ _
  let S : Finset (Finset ℕ) := (range Λ).powerset.filter (·.card ≤ ρ)
  let leaf : Finset ℕ → ClauseSet V := fun s => R.walkSeq Λ ψ₀ fun i => decide (i ∈ s)
  refine ⟨(S.image leaf).filter (Sparse θ), ?_, ?_, ?_⟩
  · -- counting position sets
    calc ((S.image leaf).filter (Sparse θ)).card ≤ (S.image leaf).card := card_filter_le _ _
      _ ≤ S.card := card_image_le
      _ ≤ ((range (ρ + 1)).biUnion fun j => (range Λ).powersetCard j).card := by
          refine card_le_card fun s hs => ?_
          obtain ⟨hsΛ, hsρ⟩ := mem_filter.mp hs
          exact mem_biUnion.mpr ⟨s.card, mem_range.mpr (by omega),
            mem_powersetCard.mpr ⟨mem_powerset.mp hsΛ, rfl⟩⟩
      _ ≤ ∑ j ∈ range (ρ + 1), ((range Λ).powersetCard j).card := card_biUnion_le
      _ = ∑ j ∈ range (ρ + 1), Λ.choose j := by
          refine sum_congr rfl fun j _ => ?_
          rw [card_powersetCard, card_range]
  · intro ψ hψ
    obtain ⟨hψimg, hsparse⟩ := mem_filter.mp hψ
    obtain ⟨s, -, rfl⟩ := mem_image.mp hψimg
    refine ⟨hsparse, fun C hC => ?_, fun x hx => ?_⟩
    · obtain ⟨D, hD, hCD⟩ := BranchingRule.refines_walkSeq (R := R) hθ C hC
      exact ⟨D, reduce_subset φ hD, hCD⟩
    · exact sat_reduce_iff.mp (BranchingRule.sat_of_sat_walkSeq (R := R) hx)
  · intro x hx
    obtain ⟨w, hw, hwx⟩ :=
      BranchingRule.exists_isLeafWord_sat (R := R) hθ ψ₀ (sat_reduce_iff.mpr hx)
    have hlen : w.length ≤ Λ := by
      simpa [card_univ] using hw.length_le hk hα (reduced_reduce φ) hψ₀ univ hU
    set s := (range w.length).filter fun i => w.getD i false = true
    have hs : s ∈ S := by
      refine mem_filter.mpr ⟨mem_powerset.mpr fun i hi => ?_, ?_⟩
      · exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp (mem_filter.mp hi).1) hlen)
      · refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
        rw [mul_comm]
        have := hw.mul_card_le hk hα (reduced_reduce φ) hψ₀ univ hU
        rwa [card_univ] at this
    have hleaf : leaf s = R.walk ψ₀ w := by
      refine BranchingRule.walkSeq_eq_walk hw (fun i hi => ?_) hlen
      simp only [s, mem_filter, mem_range, hi, true_and]
      cases w.getD i false <;> simp
    refine ⟨leaf s, mem_filter.mpr ⟨mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩, hleaf ▸ hwx⟩
    rw [hleaf]
    exact hw.sparse_walk

/-- **Bounded occurrences.** In a sparse clause set of width `k`, every variable occurs in at most
`2 ∑_{c < k} θ c` clauses. -/
theorem occurrences_le_of_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V}
    (hsparse : Sparse θ ψ) (hk : ∀ C ∈ ψ, C.card ≤ k) (v : V) :
    ψ.occurrences v ≤ 2 * ∑ c ∈ range k, θ c := by
  have hsub : ψ.filter (fun C => ∃ l ∈ C, l.1 = v) ⊆
      (univ : Finset Bool).biUnion fun p =>
        (Ico 1 (k + 1)).biUnion fun c => flower ψ c {⟨v, p⟩} := by
    intro C hC
    obtain ⟨hCψ, l, hl, hlv⟩ := mem_filter.mp hC
    have hCpos : 1 ≤ C.card := card_pos.mpr ⟨l, hl⟩
    have hleq : l = ⟨v, l.2⟩ := by cases l; simp_all
    refine mem_biUnion.mpr ⟨l.2, mem_univ _, mem_biUnion.mpr ⟨C.card,
      mem_Ico.mpr ⟨hCpos, by have := hk C hCψ; omega⟩, mem_flower.mpr ⟨hCψ, rfl, ?_⟩⟩⟩
    rw [singleton_subset_iff, ← hleq]
    exact hl
  calc ψ.occurrences v ≤ ((univ : Finset Bool).biUnion fun p =>
        (Ico 1 (k + 1)).biUnion fun c => flower ψ c {⟨v, p⟩}).card := card_le_card hsub
    _ ≤ ∑ p : Bool, ((Ico 1 (k + 1)).biUnion fun c => flower ψ c {⟨v, p⟩}).card :=
        card_biUnion_le
    _ ≤ ∑ _p : Bool, ∑ c ∈ Ico 1 (k + 1), θ (c - 1) := by
        refine sum_le_sum fun p _ => card_biUnion_le.trans (sum_le_sum fun c hc => ?_)
        exact card_flower_singleton_le_of_sparse hθ hsparse (mem_Ico.mp hc).1 _
    _ = 2 * ∑ c ∈ range k, θ c := by
        rw [sum_const, card_univ, Fintype.card_bool, smul_eq_mul, sum_Ico_eq_sum_range]
        simp

/-- **Sparse clause sets are small.** A sparse clause set of width `k` over the `N` variables of
`U` has at most `2 (∑_{c < k} θ c) N + 1` clauses: every clause but the empty one mentions a
variable. -/
theorem card_le_of_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V}
    (hsparse : Sparse θ ψ) (hk : ∀ C ∈ ψ, C.card ≤ k) (U : Finset V)
    (hU : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ U) :
    ψ.card ≤ 2 * (∑ c ∈ range k, θ c) * U.card + 1 := by
  have hsub : ψ ⊆ insert ∅ (U.biUnion fun v => ψ.filter fun C => ∃ l ∈ C, l.1 = v) := by
    intro C hC
    rcases C.eq_empty_or_nonempty with rfl | ⟨l, hl⟩
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_biUnion.mpr ⟨l.1, hU C hC l hl, mem_filter.mpr ⟨hC, l, hl, rfl⟩⟩)
  calc ψ.card ≤ (insert ∅ (U.biUnion fun v => ψ.filter fun C => ∃ l ∈ C, l.1 = v)).card :=
        card_le_card hsub
    _ ≤ (U.biUnion fun v => ψ.filter fun C => ∃ l ∈ C, l.1 = v).card + 1 := card_insert_le _ _
    _ ≤ (∑ v ∈ U, ψ.occurrences v) + 1 := Nat.add_le_add_right card_biUnion_le _
    _ ≤ (∑ _v ∈ U, 2 * ∑ c ∈ range k, θ c) + 1 :=
        Nat.add_le_add_right (sum_le_sum fun v _ => occurrences_le_of_sparse hθ hsparse hk v) _
    _ = 2 * (∑ c ∈ range k, θ c) * U.card + 1 := by rw [sum_const, smul_eq_mul, Nat.mul_comm]

end Cslib.Logic.PL.ClauseSet.Sparsification
