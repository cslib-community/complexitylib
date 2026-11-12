/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests for Copositivity)

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Encoding
public import CslibFrontier.Computability.Complexity.Problems.Copositivity
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MotzkinStraus
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Copositive
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.List.DotProduct
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Motzkin–Straus and matrix copositivity

Nonvacuous checks covering:
- `SimpleGraph.isGreatest_quadraticForm_adjMatrix`, `SimpleGraph.sSup_quadraticForm_adjMatrix`,
  and `SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff` on `K_3`, `C_4`,
  and `⊥` (`Fin 3`);
- concrete copositive and non-copositive `SymRatMatrix` instances and `NonCopositive.check`;
- concrete instantiation of `Matrix.exists_nat_dotProduct_lt_zero_of_isSymm`;
- positive and negative `cliqueToSymRatMatrix` evaluations (and boundary cases `k = 0`, `k = 1`,
  empty graph);
- headline complexity results (`NonCopositive_npComplete`, `Copositive_coNPComplete`,
  `polyTimeReducible_Clique_NonCopositive`) and `encRatArithCircuitInput`.
-/

public section

namespace CslibFrontierTests.Copositivity

open Matrix SimpleGraph Cslib.Complexity Cslib.Circuits Turing.MultiTapeTM

/-! ### Headline complexity results -/

example :
    NonCopositive ∈ NP encSymRatMatrix ∧
    NPHard encSymRatMatrix NonCopositive ∧
    NPComplete encSymRatMatrix NonCopositive ∧
    Copositive ∈ coNP encSymRatMatrix ∧
    coNPHard encSymRatMatrix Copositive ∧
    coNPComplete encSymRatMatrix Copositive ∧
    PolyTimeReducible encClique encSymRatMatrix Clique NonCopositive :=
  ⟨NonCopositive_npComplete.1, NonCopositive_npComplete.2, NonCopositive_npComplete,
    Copositive_coNPComplete.1, Copositive_coNPComplete.2, Copositive_coNPComplete,
    polyTimeReducible_Clique_NonCopositive⟩

/-! ### Motzkin–Straus on concrete graphs (`K_3`, `C_4`, `⊥`) -/

theorem cliqueNum_top_fin3 : (⊤ : SimpleGraph (Fin 3)).cliqueNum = 3 := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ := (⊤ : SimpleGraph (Fin 3)).exists_isNClique_cliqueNum
    rw [← hS.card_eq]
    simpa only [Fintype.card_fin] using Finset.card_le_univ S
  · have hclique : (⊤ : SimpleGraph (Fin 3)).IsClique (Finset.univ : Finset (Fin 3)) :=
      fun _ _ _ _ huv => huv
    simpa only [Finset.coe_univ, Finset.card_univ, Fintype.card_fin] using
      hclique.card_le_cliqueNum

-- On `K_3`, `sSup_{x : StdSimplex ℝ (Fin 3)} xᵀ A_{K_3} x = 1 - 1 / 3 = 2 / 3`.
example :
    sSup (Set.range fun x : Convexity.StdSimplex ℝ (Fin 3) =>
      (x.weights : Fin 3 → ℝ) ⬝ᵥ (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ *ᵥ
        (x.weights : Fin 3 → ℝ)) = 2 / 3 := by
  rw [SimpleGraph.sSup_quadraticForm_adjMatrix (⊤ : SimpleGraph (Fin 3)), cliqueNum_top_fin3]
  norm_num

-- Copositivity characterization on `K_3`: `copositiveCliqueMatrix ⊤ 3` is non-copositive while
-- `copositiveCliqueMatrix ⊤ 4` is copositive.
example :
    (∃ x : Fin 3 → ℚ, (∀ v, 0 ≤ x v) ∧
      x ⬝ᵥ (((⊤ : SimpleGraph (Fin 3)).copositiveCliqueMatrix 3).map (Int.cast : ℤ → ℚ) *ᵥ x) < 0) ∧
    (((⊤ : SimpleGraph (Fin 3)).copositiveCliqueMatrix 4).map (Int.cast : ℤ → ℚ)).IsCopositive := by
  constructor
  · rw [SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff
      (⊤ : SimpleGraph (Fin 3)) (by omega : 2 ≤ 3), cliqueNum_top_fin3]
  · intro x hx
    by_contra hlt
    push Not at hlt
    have h := (SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff
      (K := ℚ) (⊤ : SimpleGraph (Fin 3)) (by omega : 2 ≤ 4)).1 ⟨x, hx, hlt⟩
    rw [cliqueNum_top_fin3] at h
    omega

private def c4Adj (i j : Fin 4) : Bool :=
  (i.1 + 1) % 4 == j.1 || (j.1 + 1) % 4 == i.1

private def c4Graph : SimpleGraph (Fin 4) where
  Adj i j := c4Adj i j = true
  symm := ⟨fun i j h => by
    dsimp only [c4Adj] at h ⊢
    rw [Bool.or_comm]
    exact h⟩
  loopless := ⟨fun i h => by fin_cases i <;> revert h <;> decide⟩

private instance : DecidableRel c4Graph.Adj := fun i j =>
  inferInstanceAs (Decidable (c4Adj i j = true))

private theorem c4_no_triangle (S : Finset (Fin 4)) (hS : c4Graph.IsClique (S : Set (Fin 4))) :
    S.card ≤ 2 := by
  classical
  have h02 : (S ∩ {0, 2}).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha.2 with rfl | rfl <;> rcases hb.2 with rfl | rfl
    · rfl
    · exact absurd (hS ha.1 hb.1 (by decide)) (by decide)
    · exact absurd (hS ha.1 hb.1 (by decide)) (by decide)
    · rfl
  have h13 : (S ∩ {1, 3}).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha.2 with rfl | rfl <;> rcases hb.2 with rfl | rfl
    · rfl
    · exact absurd (hS ha.1 hb.1 (by decide)) (by decide)
    · exact absurd (hS ha.1 hb.1 (by decide)) (by decide)
    · rfl
  have hsub : S ⊆ (S ∩ {0, 2}) ∪ (S ∩ {1, 3}) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    fin_cases x <;> simp only [hx, true_and] <;> decide
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

private theorem cliqueNum_c4 : c4Graph.cliqueNum = 2 := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ := c4Graph.exists_isNClique_cliqueNum
    rw [← hS.card_eq]
    exact c4_no_triangle S hS.isClique
  · have hclique : c4Graph.IsClique (({0, 1} : Finset (Fin 4)) : Set (Fin 4)) := by
      intro u hu v hv huv
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · decide
      · decide
      · exact absurd rfl huv
    simpa only [Finset.card_pair (by decide : (0 : Fin 4) ≠ 1)] using
      hclique.card_le_cliqueNum

-- On `C_4`, `max_{x : StdSimplex ℚ (Fin 4)} xᵀ A_{C_4} x = 1 - 1 / 2 = 1 / 2`.
example :
    IsGreatest (Set.range fun x : Convexity.StdSimplex ℚ (Fin 4) =>
      (x.weights : Fin 4 → ℚ) ⬝ᵥ c4Graph.adjMatrix ℚ *ᵥ (x.weights : Fin 4 → ℚ)) (1 / 2) := by
  have h := SimpleGraph.isGreatest_quadraticForm_adjMatrix (K := ℚ) c4Graph
  rw [cliqueNum_c4] at h
  norm_num at h
  exact h

theorem cliqueNum_bot_fin3 : (⊥ : SimpleGraph (Fin 3)).cliqueNum = 1 := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ := (⊥ : SimpleGraph (Fin 3)).exists_isNClique_cliqueNum
    rw [← hS.card_eq]
    by_contra hgt
    have h2 : 1 < S.card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h2
    exact absurd (hS.isClique hu hv huv) (by simp only [SimpleGraph.bot_adj, not_false_eq_true])
  · have hclique : (⊥ : SimpleGraph (Fin 3)).IsClique (({0} : Finset (Fin 3)) : Set (Fin 3)) := by
      simp only [Finset.coe_singleton, SimpleGraph.isClique_singleton]
    simpa only [Finset.card_singleton] using hclique.card_le_cliqueNum

-- On the edgeless graph `⊥` on `Fin 3`,
-- `sSup_{x : StdSimplex ℝ (Fin 3)} xᵀ A_⊥ x = 1 - 1 / 1 = 0`.
example :
    sSup (Set.range fun x : Convexity.StdSimplex ℝ (Fin 3) =>
      (x.weights : Fin 3 → ℝ) ⬝ᵥ (⊥ : SimpleGraph (Fin 3)).adjMatrix ℝ *ᵥ
        (x.weights : Fin 3 → ℝ)) = 0 := by
  rw [SimpleGraph.sSup_quadraticForm_adjMatrix (⊥ : SimpleGraph (Fin 3)), cliqueNum_bot_fin3]
  norm_num

/-! ### Concrete `SymRatMatrix` copositivity and bounded witness verification -/

private def posMat2 : SymRatMatrix where
  rows := [[1, -1 / 2], [-1 / 2, 1]]
  square r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  symm i j := by
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]

private def negMat2 : SymRatMatrix where
  rows := [[1, -2], [-2, 1]]
  square r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  symm i j := by
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]

example : posMat2 ∈ Copositive := by
  intro x _
  dsimp only [SymRatMatrix.toMatrix, dotProduct, mulVec, Matrix.of_apply]
  have hlen : posMat2.rows.length = 2 := rfl
  let e : Fin posMat2.rows.length ≃ Fin 2 := Equiv.cast (congrArg Fin hlen)
  rw [← Equiv.sum_comp e.symm]
  rw [Fin.sum_univ_two]
  have hrow : ∀ i : Fin 2,
      (∑ j : Fin posMat2.rows.length,
        (posMat2.rows.getD (e.symm i).1 []).getD j.1 0 * x j) =
      ∑ j : Fin 2, (posMat2.rows.getD i.1 []).getD j.1 0 * x (e.symm j) := by
    intro i
    rw [← Equiv.sum_comp e.symm]
    rfl
  rw [hrow 0, hrow 1, Fin.sum_univ_two, Fin.sum_univ_two]
  have h00 : (posMat2.rows.getD 0 []).getD 0 0 = (1 : ℚ) := by
    simp only [posMat2, List.getD_cons_zero]
  have h01 : (posMat2.rows.getD 0 []).getD 1 0 = (-1 / 2 : ℚ) := by
    simp only [posMat2, List.getD_cons_zero, List.getD_cons_succ]
  have h10 : (posMat2.rows.getD 1 []).getD 0 0 = (-1 / 2 : ℚ) := by
    simp only [posMat2, List.getD_cons_zero, List.getD_cons_succ]
  have h11 : (posMat2.rows.getD 1 []).getD 1 0 = (1 : ℚ) := by
    simp only [posMat2, List.getD_cons_zero, List.getD_cons_succ]
  simp only [Fin.val_zero, Fin.val_one, h00, h01, h10, h11]
  have hid :
      x (e.symm 0) * (1 * x (e.symm 0) + -1 / 2 * x (e.symm 1)) +
          x (e.symm 1) * (-1 / 2 * x (e.symm 0) + 1 * x (e.symm 1)) =
        (x (e.symm 0) - x (e.symm 1) / 2) ^ 2 + 3 / 4 * (x (e.symm 1)) ^ 2 := by
    ring
  rw [hid]
  positivity

example : NonCopositive.check posMat2 [1, 1] = false := by
  have h12 : (-1 / 2 : ℚ) = mkRat (-1) 2 := by rw [Rat.mkRat_eq_div]; norm_num
  have hn12 : (-1 / 2 : ℚ).num = -1 := by rw [h12]; decide
  have hd12 : (-1 / 2 : ℚ).den = 2 := by rw [h12]; decide
  have hn1 : (1 : ℚ).num = 1 := rfl
  have hd1 : (1 : ℚ).den = 1 := rfl
  dsimp only [NonCopositive.check, SymRatMatrix.intRows, SymRatMatrix.commonDenom, posMat2]
  simp only [List.length_cons, List.length_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, hn12, hd12, hn1, hd1, Nat.cast_one]
  norm_num only
  have hv : ([1, 1] : List ℤ) = List.ofFn ![1, 1] := rfl
  have hr0 : ([4, -2] : List ℤ) = List.ofFn ![4, -2] := rfl
  have hr1 : ([-2, 4] : List ℤ) = List.ofFn ![-2, 4] := rfl
  rw [hv, hr0, hr1, Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn,
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn]
  have h2 : [∑ i, ![(4 : ℤ), -2] i * ![1, 1] i, ∑ i, ![(-2 : ℤ), 4] i * ![1, 1] i] =
      List.ofFn ![2, 2] := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h2, Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

example : negMat2 ∈ NonCopositive := by
  intro hcop
  have h := hcop (fun _ => 1) fun _ => by norm_num
  dsimp only [SymRatMatrix.toMatrix, dotProduct, mulVec, Matrix.of_apply] at h
  have hlen : negMat2.rows.length = 2 := rfl
  let e : Fin negMat2.rows.length ≃ Fin 2 := Equiv.cast (congrArg Fin hlen)
  rw [← Equiv.sum_comp e.symm] at h
  rw [Fin.sum_univ_two] at h
  have hrow : ∀ i : Fin 2,
      (∑ j : Fin negMat2.rows.length,
        (negMat2.rows.getD (e.symm i).1 []).getD j.1 0 * 1) =
      ∑ j : Fin 2, (negMat2.rows.getD i.1 []).getD j.1 0 * (1 : ℚ) := fun i => by
    rw [← Equiv.sum_comp e.symm]
    rfl
  rw [hrow 0, hrow 1, Fin.sum_univ_two, Fin.sum_univ_two] at h
  simp only [negMat2, Fin.val_zero, Fin.val_one, List.getD_cons_zero, List.getD_cons_succ] at h
  norm_num at h

example : NonCopositive.check negMat2 [1, 1] = true := by
  have hn2 : (-2 : ℚ).num = -2 := by decide
  have hd2 : (-2 : ℚ).den = 1 := by decide
  have hn1 : (1 : ℚ).num = 1 := rfl
  have hd1 : (1 : ℚ).den = 1 := rfl
  dsimp only [NonCopositive.check, SymRatMatrix.intRows, SymRatMatrix.commonDenom, negMat2]
  simp only [List.length_cons, List.length_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, hn2, hd2, hn1, hd1, Nat.cast_one]
  norm_num only
  have hv : ([1, 1] : List ℤ) = List.ofFn ![1, 1] := rfl
  have hr0 : ([1, -2] : List ℤ) = List.ofFn ![1, -2] := rfl
  have hr1 : ([-2, 1] : List ℤ) = List.ofFn ![-2, 1] := rfl
  rw [hv, hr0, hr1, Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn,
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn]
  have h2 : [∑ i, ![(1 : ℤ), -2] i * ![1, 1] i, ∑ i, ![(-2 : ℤ), 1] i * ![1, 1] i] =
      List.ofFn ![-1, -1] := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h2, Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

-- Concrete instantiation of `Matrix.exists_nat_dotProduct_lt_zero_of_isSymm` on a symmetric
-- integer matrix `!![1, -2; -2, 1]`.
example :
    ∃ p : Fin 2 → ℕ,
      (∀ i, p i ≤ Nat.factorial 2 * (2 * (max 2 1) ^ 2 + 1) ^ 2) ∧
        (fun i => (p i : ℤ)) ⬝ᵥ ((!![(1 : ℤ), -2; -2, 1]) *ᵥ fun i => (p i : ℤ)) < 0 := by
  have hsymm : (!![(1 : ℤ), -2; -2, 1]).IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hB : ∀ i j : Fin 2, |(!![(1 : ℤ), -2; -2, 1]) i j| ≤ 2 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  simpa only [Fintype.card_fin] using Matrix.exists_nat_dotProduct_lt_zero_of_isSymm hsymm hB (by
    intro hcop
    have h := hcop (fun _ => 1) fun _ => by norm_num
    simp only [dotProduct, mulVec, Matrix.map_apply] at h
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] at h)

-- Arbitrary finite index type instantiation of `Matrix.exists_nat_dotProduct_lt_zero_of_isSymm`
-- on `Bool`.
example :
    ∃ p : Bool → ℕ,
      (∀ b, p b ≤
          Nat.factorial (Fintype.card Bool) *
            (Fintype.card Bool * (max 2 1) ^ 2 + 1) ^ Fintype.card Bool) ∧
        (fun b => (p b : ℤ)) ⬝ᵥ
          ((Matrix.of fun a b : Bool => if a = b then (1 : ℤ) else -2) *ᵥ
            fun b => (p b : ℤ)) < 0 := by
  let M : Matrix Bool Bool ℤ := Matrix.of fun a b => if a = b then (1 : ℤ) else -2
  have hsymm : M.IsSymm := by
    ext a b
    simp only [M, transpose_apply, Matrix.of_apply, eq_comm]
  have hB : ∀ a b : Bool, |M a b| ≤ 2 := by
    intro a b
    cases a <;> cases b <;> norm_num [M]
  refine Matrix.exists_nat_dotProduct_lt_zero_of_isSymm hsymm hB ?_
  intro hcop
  have h := hcop (fun _ => 1) fun _ => by norm_num
  simp only [dotProduct, mulVec, Matrix.map_apply, Fintype.sum_bool, Matrix.of_apply] at h
  norm_num at h

/-! ### Reduction instances (`cliqueToSymRatMatrix`) -/

private def triangleG : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩

private def path3G : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2)]⟩

private def emptyG : Graph := ⟨[], []⟩

example : cliqueToSymRatMatrix (triangleG, 3) ∈ NonCopositive := by
  rw [← cliqueToSymRatMatrix_mem_iff, mem_Clique_iff]
  refine ⟨{0, 1, 2}, fun v hv => by
    simp only [triangleG, List.mem_cons, List.not_mem_nil, or_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    exact hv, ?_⟩
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, by decide⟩
  intro u hu v hv huv
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hu hv
  rw [← Graph.adjBool_eq_true_iff]
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first | exact absurd rfl huv | decide

example : cliqueToSymRatMatrix (path3G, 3) ∈ Copositive := by
  rw [Copositive_eq_compl, Set.mem_compl_iff, ← cliqueToSymRatMatrix_mem_iff, mem_Clique_iff]
  rintro ⟨S, hSG, hS⟩
  have hsub : S ⊆ ({0, 1, 2} : Finset ℕ) := by
    intro v hv
    have hv' := hSG v hv
    simp only [path3G, List.mem_cons, List.not_mem_nil, or_false] at hv'
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hv'
  have hcard : S.card = 3 := hS.card_eq
  have heq : S = {0, 1, 2} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
  rw [heq] at hS
  have hadj : path3G.toSimpleGraph.Adj 0 2 :=
    hS.isClique (by decide) (by decide) (by decide)
  rw [← Graph.adjBool_eq_true_iff] at hadj
  revert hadj
  decide

example : cliqueToSymRatMatrix (emptyG, 0) ∈ NonCopositive := by
  rw [← cliqueToSymRatMatrix_mem_iff, mem_Clique_iff]
  refine ⟨∅, fun _ h => absurd h (Finset.notMem_empty _), ?_⟩
  simp only [SimpleGraph.isNClique_iff, Finset.coe_empty, SimpleGraph.isClique_empty,
    Finset.card_empty, and_self]

example : cliqueToSymRatMatrix (emptyG, 1) ∈ Copositive := by
  rw [Copositive_eq_compl, Set.mem_compl_iff, ← cliqueToSymRatMatrix_mem_iff, mem_Clique_iff]
  rintro ⟨S, hSG, hS⟩
  have hpos : 0 < S.card := by rw [hS.card_eq]; omega
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
  have hv0 := hSG v hv
  simp only [emptyG, List.not_mem_nil] at hv0

/-! ### Optional rational arithmetic circuit input encoding and `PolyTime.Rat` -/

example : ComputableInPolyTime Rat.num encRat encIntBin := by fun_prop

example : ComputableInPolyTime Rat.den encRat encNat := by fun_prop

example : ComputableInPolyTime (fun z : ℤ => (z : ℚ)) encIntBin encRat := by fun_prop

example :
    let c : Σ n, Circuit (arithSignature ℚ) n 1 :=
      ⟨1, Circuit.mk Program.empty fun _ => Wire.input ⟨0, by omega⟩⟩
    0 < (encRatArithCircuitInput 1 (c, [1 / 2, -3 / 4])).length := by
  intro c
  dsimp only [encRatArithCircuitInput]
  rw [encPair_apply, List.length_append]
  dsimp only
  have hpos : 0 < (encList encRat [1 / 2, -3 / 4]).length := by
    have hge :=
      SizedListEncoding.length_le (encA := encRat) (encL := encList encRat) [1 / 2, -3 / 4]
    have hlen : ([1 / 2, -3 / 4] : List ℚ).length = 2 := rfl
    change 2 ≤ (encList encRat [1 / 2, -3 / 4]).length at hge
    omega
  omega

end CslibFrontierTests.Copositivity
