/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Simplex.LinearProgram
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Two-phase simplex method

This module implements the two-phase simplex method for linear programs
`max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x ≤ b`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.unreachableTactic false

public section

namespace Cslib.Algorithms.Lean.Simplex

open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

/-- The outcome of the two-phase simplex method. -/
inductive TwoPhaseResult (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
  /-- The program is infeasible, certified by a Farkas certificate `y`. -/
  | infeasible (y : Fin m → K)
  /-- The program is unbounded, certified by a feasible ray `d` and a feasible point `x`. -/
  | unbounded (x d : Fin n → K)
  /-- The program is optimal, with primal solution `x` and dual solution `y`. -/
  | optimal (x : Fin n → K) (y : Fin m → K)

/-- The auxiliary matrix `[A | -1]` for Phase I. -/
def auxMatrix (A : Matrix (Fin m) (Fin n) K) : Matrix (Fin m) (Fin (n + 1)) K :=
  Matrix.of fun i j => if hj : j.val < n then A i ⟨j.val, hj⟩ else -1

/-- The objective for Phase I: `max -x₀`. -/
def auxObj : Fin (n + 1) → K :=
  fun j => if j.val < n then 0 else -1

/-- The auxiliary Phase I dictionary. -/
def auxDictionary (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    Dictionary (Fin (n + 1 + m)) K :=
  slackDictionary (auxMatrix A) b auxObj

/-- The index of `x₀` in the auxiliary dictionary. -/
def x₀Index : Fin (n + 1 + m) := Fin.castAdd m (Fin.last n)

/-- The index of the slack variable for row `i` in the auxiliary dictionary. -/
def slackIndex (i : Fin m) : Fin (n + 1 + m) := Fin.natAdd (n + 1) i

/-- Finds the index `r : Fin m` minimizing `b r`. -/
def minRhsIndex (b : Fin m → K) : Option (Fin m) :=
  match minOpt (Finset.image b Finset.univ) with
  | none => none
  | some min_val => minOpt (Finset.univ.filter fun i => b i = min_val)

/-- Phase I initial feasible dictionary. -/
def phaseOneDict (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) : Dictionary (Fin (n + 1 + m)) K :=
  match minRhsIndex b with
  | none => auxDictionary A b
  | some r =>
    if b r < 0 then
      (auxDictionary A b).pivot (slackIndex r) x₀Index
    else
      auxDictionary A b

def unskipX₀ (i : Fin (n + 1 + m)) (hi : i ≠ x₀Index) : Fin (n + m) :=
  if h : i.val < n then
    ⟨i.val, by omega⟩
  else
    ⟨i.val - 1, by
      have h1 : i.val ≠ n := by intro heq; apply hi; apply Fin.ext; exact heq
      clear hi
      omega⟩

def skipX₀ (i : Fin (n + m)) : Fin (n + 1 + m) :=
  if h : i.val < n then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- Drop `x₀` from the dictionary and install the original objective `c`. -/
def dropX₀ (D : Dictionary (Fin (n + 1 + m)) K) (c : Fin n → K) : Dictionary (Fin (n + m)) K where
  basis := Finset.image (fun (i : {x // x ∈ D.basis.erase x₀Index}) =>
    unskipX₀ i.val (Finset.ne_of_mem_erase i.prop)) (D.basis.erase x₀Index).attach
  rhs i := D.rhs (skipX₀ i)
  coeff i j := D.coeff (skipX₀ i) (skipX₀ j)
  objConst := ∑ j : Fin n,
    if skipX₀ (Fin.castAdd m j) ∈ D.basis then
      c j * D.rhs (skipX₀ (Fin.castAdd m j))
    else 0
  objCoeff k := (if hk : k.val < n then c ⟨k.val, hk⟩ else 0) +
    ∑ j : Fin n,
      if skipX₀ (Fin.castAdd m j) ∈ D.basis then
        c j * D.coeff (skipX₀ (Fin.castAdd m j)) (skipX₀ k)
      else 0

/-- Perform a degenerate pivot to remove `x₀` from the basis if it is basic. -/
def forcePivotX₀ (D : Dictionary (Fin (n + 1 + m)) K) : Dictionary (Fin (n + 1 + m)) K :=
  if x₀Index ∈ D.basis then
    match minOpt (D.basisᶜ.filter (fun j => D.coeff x₀Index j ≠ 0)) with
    | none => D
    | some j => D.pivot x₀Index j
  else D

/-- Extract Phase I result and prepare Phase II. -/
def phaseOneExtract (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) :
    TwoPhaseResult A b c ⊕ Dictionary (Fin (n + m)) K :=
  match (phaseOneDict A b).simplex with
  | .optimal D =>
    if D.objConst < 0 then
      .inl (.infeasible D.slackDual)
    else
      .inr (dropX₀ (forcePivotX₀ D) c)
  | .unbounded _ _ => .inl (.infeasible 0) -- unreachable
  | .outOfFuel _ => .inl (.infeasible 0) -- unreachable

/-- The total two-phase simplex method returning terminating certificates. -/
def twoPhase (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) : TwoPhaseResult A b c :=
  match phaseOneExtract A b c with
  | .inl res => res
  | .inr D =>
    match D.simplex with
    | .optimal D' =>
      TwoPhaseResult.optimal (fun j => D'.basicSolution (Fin.castAdd m j)) D'.slackDual
    | .unbounded D' s =>
      TwoPhaseResult.unbounded (fun j => D'.basicSolution (Fin.castAdd m j)) (fun j => D'.ray s (Fin.castAdd m j))
    | .outOfFuel _ => TwoPhaseResult.infeasible 0 -- unreachable

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem auxDictionary_coeff_k (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (k : Fin m) :
    (auxDictionary A b).coeff (slackIndex k) x₀Index = 1 := by
  dsimp [auxDictionary, slackDictionary, slackIndex, x₀Index, Fin.append]
  rw [Fin.addCases_right, Fin.addCases_left]
  have h_matrix : auxMatrix A k (Fin.last n) = -1 := by
    dsimp [auxMatrix]
    have h_lt : ¬ (Fin.last n).val < n := by
      have h_val : (Fin.last n).val = n := rfl
      omega
    exact dite_eq_right h_lt
  rw [h_matrix]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem auxDictionary_rhs_k (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (k : Fin m) :
    (auxDictionary A b).rhs (slackIndex k) = b k := by
  dsimp [auxDictionary, slackDictionary, slackIndex, Fin.append]
  rw [Fin.addCases_right]

theorem phaseOneDict_feasible (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (phaseOneDict A b).Feasible := by
  dsimp [phaseOneDict]
  cases h_min : minRhsIndex b
  · dsimp only
    intro i hi
    have h_m : m = 0 := by
      unfold minRhsIndex at h_min
      cases h_opt : minOpt (Finset.image b Finset.univ)
      · rw [h_opt] at h_min
        have h_empty := minOpt_eq_none_iff.1 h_opt
        rw [Finset.image_eq_empty] at h_empty
        by_contra h_m
        have : Nonempty (Fin m) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero h_m)
        exact Finset.univ_nonempty.ne_empty h_empty
      · rename_i min_val
        rw [h_opt] at h_min
        have h_v := minOpt_eq_some_iff.1 h_opt
        have h_mem : min_val ∈ Finset.image b Finset.univ := h_v.1
        rw [Finset.mem_image] at h_mem
        rcases h_mem with ⟨j, _, hj_eq⟩
        have h_empty := minOpt_eq_none_iff.1 h_min
        have h_j_in : j ∈ Finset.univ.filter (fun x => b x = min_val) := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ j, hj_eq⟩
        have h_absurd : j ∈ (∅ : Finset (Fin m)) := h_empty ▸ h_j_in
        simp at h_absurd
    have h_mem2 : n + 1 ≤ i.val := by
      dsimp [auxDictionary, slackDictionary] at hi
      rw [Finset.mem_filter] at hi
      exact hi.2
    have h_lt : i.val < n + 1 + m := i.isLt
    omega
  · rename_i r
    dsimp only
    have h_min_spec : ∀ j : Fin m, b r ≤ b j := by
      unfold minRhsIndex at h_min
      cases h_opt : minOpt (Finset.image b Finset.univ)
      · rw [h_opt] at h_min; contradiction
      · rw [h_opt] at h_min
        rename_i min_val
        have h_min_val := minOpt_eq_some_iff.1 h_opt
        have h_r := minOpt_eq_some_iff.1 h_min
        have hr1 : b r = min_val := by
          have h1 := h_r.1
          rw [Finset.mem_filter] at h1
          exact h1.2
        intro k
        rw [hr1]
        apply h_min_val.2
        rw [Finset.mem_image]
        exact ⟨k, Finset.mem_univ k, rfl⟩
    split_ifs with h_lt
    · intro i hi
      have h_basis : i ∈ insert x₀Index ((auxDictionary A b).basis.erase (slackIndex r)) := hi
      rw [Finset.mem_insert, Finset.mem_erase] at h_basis
      rcases h_basis with rfl | ⟨h_ne, h_mem⟩
      · have h_rhs : ((auxDictionary A b).pivot (slackIndex r) x₀Index).rhs x₀Index = - (auxDictionary A b).rhs (slackIndex r) / (auxDictionary A b).coeff (slackIndex r) x₀Index := by
          dsimp [Dictionary.pivot]
          rw [ite_eq_left rfl]
        rw [h_rhs, auxDictionary_rhs_k A b r, auxDictionary_coeff_k A b r]
        have hb : -b r / 1 = -b r := by ring
        rw [hb]
        linarith
      · have h_rhs : ((auxDictionary A b).pivot (slackIndex r) x₀Index).rhs i = (auxDictionary A b).rhs i - (auxDictionary A b).coeff i x₀Index * (auxDictionary A b).rhs (slackIndex r) / (auxDictionary A b).coeff (slackIndex r) x₀Index := by
          dsimp [Dictionary.pivot]
          have h_if : i ≠ x₀Index := by
            intro heq
            dsimp [auxDictionary, slackDictionary, x₀Index] at heq h_mem
            rw [Finset.mem_filter] at h_mem
            have h1 := h_mem.2
            have h2 : i.val = n := by rw [heq]; rfl
            omega
          rw [ite_eq_right h_if, ite_eq_left ⟨h_mem, h_ne⟩]
        rw [h_rhs]
        have hk : ∃ k : Fin m, i.val = n + 1 + k.val := by
          dsimp [auxDictionary, slackDictionary] at h_mem
          rw [Finset.mem_filter] at h_mem
          have h_mem2 : n + 1 ≤ i.val := h_mem.2
          have h_lt_b : i.val < n + 1 + m := i.isLt
          have h_lt2 : i.val - (n + 1) < m := by omega
          have h_eq : i.val = n + 1 + (i.val - (n + 1)) := by omega
          exact ⟨⟨i.val - (n + 1), h_lt2⟩, h_eq⟩
        rcases hk with ⟨k, hk_val⟩
        have h_eq : i = slackIndex k := by ext; exact hk_val
        rw [h_eq, auxDictionary_rhs_k A b r, auxDictionary_coeff_k A b r, auxDictionary_rhs_k A b k, auxDictionary_coeff_k A b k]
        have hb : b k - 1 * b r / 1 = b k - b r := by ring
        rw [hb]
        exact sub_nonneg.2 (h_min_spec k)
    · intro i hi
      have hk : ∃ k : Fin m, i.val = n + 1 + k.val := by
        dsimp [auxDictionary, slackDictionary] at hi
        rw [Finset.mem_filter] at hi
        have h_mem2 : n + 1 ≤ i.val := hi.2
        have h_lt_b : i.val < n + 1 + m := i.isLt
        have h_lt2 : i.val - (n + 1) < m := by omega
        have h_eq : i.val = n + 1 + (i.val - (n + 1)) := by omega
        exact ⟨⟨i.val - (n + 1), h_lt2⟩, h_eq⟩
      rcases hk with ⟨k, hk_val⟩
      have h_eq : i = slackIndex k := by ext; exact hk_val
      rw [h_eq, auxDictionary_rhs_k A b k]
      linarith [h_min_spec k]


private theorem slackDual_spec_of_equiv (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
    {D : Dictionary (Fin (n + m)) K}
    (hequiv : D.Equivalent (slackDictionary A b c))
    (hopt : ∀ j ∉ D.basis, D.objCoeff j ≤ 0) :
    0 ≤ D.slackDual ∧ c ≤ D.slackDual ᵥ* A ∧ D.slackDual ⬝ᵥ b = D.objConst := by
  set g : Fin (n + m) → K := fun j => if j ∈ D.basis then 0 else D.objCoeff j with hg
  have hgle : ∀ j, g j ≤ 0 := fun j => by
    simp only [hg]; split_ifs with hj
    · exact le_rfl
    · exact hopt j hj
  have hvalue : ∀ z, D.value z = D.objConst + ∑ j, g j * z j := fun z => by
    rw [Dictionary.value, ← Finset.sum_compl_add_sum D.basis, Finset.sum_eq_zero (s := D.basis)
      fun j hj => by simp only [hg, hj, ↓reduceIte, zero_mul], add_zero]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by
      simp only [hg, Finset.mem_compl.1 hj, ↓reduceIte]
  have hy : D.slackDual = fun i => -g (Fin.natAdd n i) := funext fun i => by
    simp only [Dictionary.slackDual, hg]
    split_ifs <;> simp only [neg_zero]
  set y := D.slackDual
  have key : ∀ x : Fin n → K, c ⬝ᵥ x =
      D.objConst - y ⬝ᵥ b + ∑ k, g (Fin.castAdd m k) * x k + (y ᵥ* A) ⬝ᵥ x := by
    intro x
    rw [← value_withSlack A b c, Dictionary.Equivalent.value_eq hequiv.symm _ (isSolution_withSlack A b c x), hvalue,
      Fin.sum_univ_add, ← dotProduct_mulVec, hy]
    simp only [withSlack_castAdd, withSlack_natAdd, dotProduct, mul_sub,
      Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
    simp only [sub_eq_add_neg]
    ring
  have hv : y ⬝ᵥ b = D.objConst := by
    have := key 0
    simp only [dotProduct_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero] at this
    linarith
  refine ⟨fun i => ?_, fun k => ?_, hv⟩
  · rw [hy]
    exact neg_nonneg.2 (hgle _)
  have := key (Pi.single k 1)
  rw [dotProduct_single_one, dotProduct_single_one, hv, sub_self, zero_add] at this
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one] at this
  linarith [hgle (Fin.castAdd m k)]



theorem phaseOneDict_equivalent (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (phaseOneDict A b).Equivalent (auxDictionary A b) := by
  dsimp [phaseOneDict]
  cases h : minRhsIndex b with
  | none => 
    dsimp only
    exact Equivalent.refl _
  | some r =>
    dsimp only
    split_ifs with hb
    · have hr : slackIndex r ∈ (auxDictionary A b).basis := by
        dsimp [auxDictionary, slackDictionary, slackIndex]
        rw [Finset.mem_filter]
        simp
      have hs : x₀Index ∉ (auxDictionary A b).basis := by
        dsimp [auxDictionary, slackDictionary, x₀Index]
        rw [Finset.mem_filter]
        simp
      have hc : (auxDictionary A b).coeff (slackIndex r) x₀Index ≠ 0 := by
        dsimp [auxDictionary, slackDictionary, coeff, slackIndex, x₀Index, auxMatrix]
        simp
      exact Equivalent.symm (Dictionary.equivalent_pivot (auxDictionary A b) hr hs hc)
    · exact Equivalent.refl _

private theorem auxDictionary_value_le_zero (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (z : Fin (n + 1 + m) → K) (hz1 : (auxDictionary A b).IsSolution z) (hz2 : 0 ≤ z) :
    (auxDictionary A b).value z ≤ 0 := by
  have hz := eq_withSlack_of_isSolution (auxMatrix A) b auxObj hz1
  change (slackDictionary _ _ _).value z ≤ 0
  have hz_subst : (slackDictionary (auxMatrix A) b auxObj).value z = auxObj ⬝ᵥ (fun j => z (Fin.castAdd m j)) := by
    calc (slackDictionary (auxMatrix A) b auxObj).value z
      _ = (slackDictionary (auxMatrix A) b auxObj).value (withSlack (auxMatrix A) b (fun j => z (Fin.castAdd m j))) := by congr 1
      _ = auxObj ⬝ᵥ (fun j => z (Fin.castAdd m j)) := value_withSlack (auxMatrix A) b auxObj (fun j => z (Fin.castAdd m j))
  rw [hz_subst]
  have h_eq : auxObj ⬝ᵥ (fun j => z (Fin.castAdd m j)) = ∑ i : Fin (n + 1), if i.val < n then (0 : K) else - z (Fin.castAdd m i) := by
    dsimp [auxObj, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h_i
    · rw [zero_mul]
    · rw [neg_mul, one_mul]
  rw [h_eq]
  have h_last : (∑ i : Fin (n + 1), if i.val < n then (0 : K) else - z (Fin.castAdd m i)) = - z x₀Index := by
    have h1 : Finset.univ (α := Fin (n + 1)) = insert (Fin.last n) (Finset.univ.filter (fun (i : Fin (n + 1)) => i.val < n)) := by
      ext i
      rw [Finset.mem_insert, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      by_cases hi : i.val < n
      · simp [hi]
      · have : i.val = n := by omega
        have heq : i = Fin.last n := by ext; exact this
        simp [heq]
    rw [h1, Finset.sum_insert]
    · have h_zero : (∑ i ∈ Finset.filter (fun (i : Fin (n + 1)) => i.val < n) Finset.univ, (if i.val < n then (0 : K) else - z (Fin.castAdd m i))) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_filter] at hi
        have hi_lt : i.val < n := hi.2
        simp [hi_lt]
      rw [h_zero, add_zero]
      have hnot_lt : ¬((Fin.last n).val < n) := by simp
      simp
      rfl
    · rw [Finset.mem_filter]
      simp
  rw [h_last]
  have hz_ge : 0 ≤ z x₀Index := hz2 _
  linarith

private theorem phaseOne_unbounded_unreachable (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (_ : Fin n → K)
    (D' : Dictionary (Fin (n + 1 + m)) K) (s : Fin (n + 1 + m))
    (h_sim : (phaseOneDict A b).simplex = .unbounded D' s) :
    False := by
  have h_feas := phaseOneDict_feasible A b
  obtain ⟨hequiv2, hfeas2, h_unb2⟩ := Dictionary.run_eq_unbounded (phaseOneDict A b) h_feas h_sim
  have hequivS := phaseOneDict_equivalent A b
  have h_equiv_new := Equivalent.trans (Equivalent.symm hequiv2) hequivS
  
  have hz_sol : (auxDictionary A b).IsSolution D'.basicSolution :=
    (h_equiv_new.isSolution_iff _).1 D'.isSolution_basicSolution
  have hz_ge : 0 ≤ D'.basicSolution := D'.feasible_iff_nonneg_basicSolution.1 hfeas2
  have H1 := auxDictionary_value_le_zero A b _ hz_sol hz_ge
  have H2 := h_equiv_new.value_eq _ D'.isSolution_basicSolution
  have hz_val_le : D'.value D'.basicSolution ≤ 0 := by linarith

  set t : K := (1 - D'.value D'.basicSolution) / D'.objCoeff s
  have ht_ge : 0 ≤ t := by
    have Ht1 : 0 ≤ 1 - D'.value D'.basicSolution := by linarith
    have Ht2 : 0 < D'.objCoeff s := h_unb2.2.1
    exact div_nonneg Ht1 (le_of_lt Ht2)

  set z := D'.basicSolution + t • D'.ray s
  have hz_sol_D : D'.IsSolution z := D'.isSolution_add_smul_ray h_unb2.1 D'.isSolution_basicSolution t
  have hz_sol_aux : (auxDictionary A b).IsSolution z := (h_equiv_new.isSolution_iff _).1 hz_sol_D
  have hz_ge_z : 0 ≤ z := by
    have H1_z : 0 ≤ D'.basicSolution := D'.feasible_iff_nonneg_basicSolution.1 hfeas2
    have H2_z : 0 ≤ D'.ray s := D'.ray_nonneg h_unb2.1 h_unb2.2.2
    intro i
    have H3 : 0 ≤ t * D'.ray s i := mul_nonneg ht_ge (H2_z i)
    have H4 : z i = D'.basicSolution i + t * D'.ray s i := rfl
    linarith [H1_z i, H3]

  have H_val_z_le : (auxDictionary A b).value z ≤ 0 := auxDictionary_value_le_zero A b z hz_sol_aux hz_ge_z
  have H_val_eq : D'.value z = (auxDictionary A b).value z := h_equiv_new.value_eq z hz_sol_D
  have H_val_D : D'.value z = D'.value D'.basicSolution + t * D'.objCoeff s := D'.value_add_smul_ray h_unb2.1 D'.basicSolution t
  
  have H_t_mul : t * D'.objCoeff s = 1 - D'.value D'.basicSolution := by
    exact div_mul_cancel₀ _ (ne_of_gt h_unb2.2.1)
    
  linarith

private theorem unbounded_spec_of_equiv (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
    (D D'' : Dictionary (Fin (n + m)) K)
    (hequiv : D.Equivalent (slackDictionary A b c))
    (hfeas : D.Feasible) (s : Fin (n + m))
    (h_unb : D.simplex = .unbounded D'' s) :
    let x := fun j => D''.basicSolution (Fin.castAdd m j)
    let d := fun j => D''.ray s (Fin.castAdd m j)
    0 ≤ x ∧ A *ᵥ x ≤ b ∧ 0 ≤ d ∧ A *ᵥ d ≤ 0 ∧ 0 < c ⬝ᵥ d := by
  dsimp only
  obtain ⟨hequiv2, hfeas2, h_unb2⟩ := Dictionary.run_eq_unbounded D hfeas h_unb
  have h_equiv_new := Equivalent.trans (Equivalent.symm hequiv2) hequiv
  
  set z := D''.basicSolution
  set r := D''.ray s
  have hz_sol : (slackDictionary A b c).IsSolution z :=
    (h_equiv_new.isSolution_iff _).1 D''.isSolution_basicSolution
  
  have h_mem : z ∈ (slackDictionary A b c).feasibleSet :=
    (Dictionary.mem_feasibleSet _).2 ⟨hz_sol, D''.feasible_iff_nonneg_basicSolution.1 hfeas2⟩
  
  have hz := eq_withSlack_of_isSolution A b c hz_sol
  rw [hz] at h_mem
  
  have H_sol_z_r : D''.IsSolution (z + (1 : K) • r) := D''.isSolution_add_smul_ray h_unb2.1 D''.isSolution_basicSolution (1 : K)
  have hr_sol : (slackDictionary A b c).IsSolution (z + (1 : K) • r) := by
    apply (h_equiv_new.isSolution_iff _).1
    exact H_sol_z_r
  
  have hzr : z + (1 : K) • r = withSlack A b (fun j => (z + (1 : K) • r) (Fin.castAdd m j)) :=
    eq_withSlack_of_isSolution A b c hr_sol
  
  have h_ray_nonneg : 0 ≤ r := D''.ray_nonneg h_unb2.1 h_unb2.2.2
  
  have hx1 : 0 ≤ fun j => z (Fin.castAdd m j) := by
    intro j
    have : 0 ≤ z := D''.feasible_iff_nonneg_basicSolution.1 hfeas2
    exact this _
    
  have hx2 : A *ᵥ (fun j => z (Fin.castAdd m j)) ≤ b := by
    intro i
    have : z (Fin.natAdd n i) = b i - (A *ᵥ (fun j => z (Fin.castAdd m j))) i := by
      have hz_i : z (Fin.natAdd n i) = (withSlack A b (fun j => z (Fin.castAdd m j))) (Fin.natAdd n i) := congr_fun hz _
      rw [hz_i, withSlack_natAdd]
    have hz_ge : 0 ≤ z (Fin.natAdd n i) := D''.feasible_iff_nonneg_basicSolution.1 hfeas2 _
    linarith

  refine ⟨hx1, hx2, fun j => h_ray_nonneg _, ?_, ?_⟩
  
  · intro i
    change (A *ᵥ (fun j => r (Fin.castAdd m j))) i ≤ (0 : K)
    have hz_i : z (Fin.natAdd n i) = (withSlack A b (fun j => z (Fin.castAdd m j))) (Fin.natAdd n i) := congr_fun hz _
    have hz_i2 : z (Fin.natAdd n i) = b i - (A *ᵥ (fun j => z (Fin.castAdd m j))) i := by
      rw [hz_i, withSlack_natAdd]
    
    have hzr_i : (z + (1 : K) • r) (Fin.natAdd n i) = (withSlack A b (fun j => (z + (1 : K) • r) (Fin.castAdd m j))) (Fin.natAdd n i) := congr_fun hzr _
    have hzr_i2 : (z + (1 : K) • r) (Fin.natAdd n i) = b i - (A *ᵥ (fun j => (z + (1 : K) • r) (Fin.castAdd m j))) i := by
      rw [hzr_i, withSlack_natAdd]
    
    have H1 : (z + (1 : K) • r) (Fin.natAdd n i) = z (Fin.natAdd n i) + r (Fin.natAdd n i) := by
      simp only [Pi.add_apply, one_smul]
    
    have H2 : (A *ᵥ (fun j => (z + (1 : K) • r) (Fin.castAdd m j))) i = (A *ᵥ (fun j => z (Fin.castAdd m j))) i + (A *ᵥ (fun j => r (Fin.castAdd m j))) i := by
      dsimp [mulVec, dotProduct]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [one_mul, mul_add]
      
    rw [H1, hz_i2, H2] at hzr_i2
    have H_r_ge : 0 ≤ r (Fin.natAdd n i) := h_ray_nonneg _
    linarith

  · have Hvalue : D''.value (z + (1 : K) • r) = D''.value z + (1 : K) * D''.objCoeff s := D''.value_add_smul_ray h_unb2.1 z (1 : K)
    have Hvalue_equiv1 : D''.value z = (slackDictionary A b c).value z := h_equiv_new.value_eq z D''.isSolution_basicSolution
    have Hvalue_equiv2 : D''.value (z + (1 : K) • r) = (slackDictionary A b c).value (z + (1 : K) • r) := h_equiv_new.value_eq (z + (1 : K) • r) H_sol_z_r
    
    rw [Hvalue_equiv1, Hvalue_equiv2] at Hvalue
    
    have Hc1 : (slackDictionary A b c).value z = c ⬝ᵥ (fun j => z (Fin.castAdd m j)) := by
      calc (slackDictionary A b c).value z
        _ = (slackDictionary A b c).value (withSlack A b (fun j => z (Fin.castAdd m j))) := congrArg _ hz
        _ = c ⬝ᵥ (fun j => z (Fin.castAdd m j)) := value_withSlack A b c (fun j => z (Fin.castAdd m j))
        
    have Hc2 : (slackDictionary A b c).value (z + (1 : K) • r) = c ⬝ᵥ (fun j => (z + (1 : K) • r) (Fin.castAdd m j)) := by
      calc (slackDictionary A b c).value (z + (1 : K) • r)
        _ = (slackDictionary A b c).value (withSlack A b (fun j => (z + (1 : K) • r) (Fin.castAdd m j))) := congrArg _ hzr
        _ = c ⬝ᵥ (fun j => (z + (1 : K) • r) (Fin.castAdd m j)) := value_withSlack A b c (fun j => (z + (1 : K) • r) (Fin.castAdd m j))
        
    rw [Hc1, Hc2] at Hvalue
    
    have Hdistrib : c ⬝ᵥ (fun j => (z + (1 : K) • r) (Fin.castAdd m j)) = c ⬝ᵥ (fun j => z (Fin.castAdd m j)) + c ⬝ᵥ (fun j => r (Fin.castAdd m j)) := by
      dsimp [dotProduct]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [one_mul, mul_add]
      
    rw [Hdistrib] at Hvalue
    have Hc3 : c ⬝ᵥ (fun j => r (Fin.castAdd m j)) = D''.objCoeff s := by linarith
    rw [Hc3]
    exact h_unb2.2.1

theorem extractInfeasible_spec (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (_ : Fin n → K)
    (D : Dictionary (Fin (n + 1 + m)) K)
    (hopt : (phaseOneDict A b).simplex = .optimal D)
    (hneg : D.objConst < 0) :
    let y := D.slackDual; 0 ≤ y ∧ 0 ≤ y ᵥ* A ∧ y ⬝ᵥ b < 0 := sorry

lemma aux_value_eq (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (z : Fin (n + 1 + m) → K) :
    (auxDictionary A b).value z = - z x₀Index := by
  have H : ∀ j ∈ (auxDictionary A b).basisᶜ,
    (auxDictionary A b).objCoeff j * z j = if j = x₀Index then - z x₀Index else 0 := by
    intro j hj
    dsimp [auxDictionary, slackDictionary] at hj
    rw [Finset.mem_compl, Finset.mem_filter, not_and, not_le] at hj
    have hj_cast := hj (Finset.mem_univ j)
    dsimp [auxDictionary, slackDictionary]
    have happend : Fin.append auxObj (0 : Fin m → K) j = auxObj ⟨j.val, hj_cast⟩ := by
      exact Fin.addCases_left (i := ⟨j.val, hj_cast⟩)
    rw [happend]
    dsimp [auxObj]
    by_cases h1 : j.val < n
    · have hite1 : (if j.val < n then (0 : K) else -1) = 0 := if_pos h1
      rw [hite1, zero_mul]
      have hne : j ≠ x₀Index := by
        intro heq
        have : j.val = n := by rw [heq, x₀Index]; rfl
        linarith
      have hite2 : (if j = x₀Index then - z x₀Index else (0 : K)) = 0 := if_neg hne
      rw [hite2]
    · have hite1 : (if j.val < n then (0 : K) else -1) = -1 := if_neg h1
      rw [hite1, neg_mul, one_mul]
      have heq : j = x₀Index := by
        ext
        dsimp [x₀Index]
        linarith
      have hite2 : (if j = x₀Index then - z x₀Index else (0 : K)) = - z x₀Index := if_pos heq
      rw [hite2, heq]
  rw [Dictionary.value, Finset.sum_congr rfl H]
  dsimp [auxDictionary, slackDictionary]
  rw [zero_add]
  have hx0_lt : (x₀Index : Fin (n + 1 + m)).val < n + 1 := by
    dsimp [x₀Index]
    linarith
  have hmem : x₀Index ∈ (Finset.filter (fun (i : Fin (n + 1 + m)) => n + 1 ≤ i.val) Finset.univ)ᶜ := by
    rw [Finset.mem_compl, Finset.mem_filter, not_and, not_le]
    intro _
    exact hx0_lt
  rw [Finset.sum_eq_single x₀Index]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hnot
    exfalso
    exact hnot hmem

lemma hzero_of_basis (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (D : Dictionary (Fin (n + 1 + m)) K)
    (hequiv : (auxDictionary A b).Equivalent D) (hzero : D.objConst = 0)
    (hx0 : x₀Index ∈ D.basis) :
    D.rhs x₀Index = 0 := by
  have H := hequiv.symm.value_eq D.basicSolution D.isSolution_basicSolution
  rw [value_basicSolution, hzero] at H
  have H2 := aux_value_eq A b D.basicSolution
  rw [H2] at H
  have H3 : D.basicSolution x₀Index = 0 := by linarith
  have H4 : D.basicSolution x₀Index = D.rhs x₀Index := by
    dsimp [Dictionary.basicSolution]
    rw [if_pos hx0]
  rw [H4] at H3
  exact H3

lemma aux_shift_solution (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (z : Fin (n + 1 + m) → K)
    (hz : (auxDictionary A b).IsSolution z) :
    let y := fun (j : Fin (n + 1 + m)) => z j + if j = x₀Index then (1 : K) else if n + 1 ≤ j.val then 1 else 0
    (auxDictionary A b).IsSolution y := by
  intro y i hbasis
  have hz_i := hz i hbasis
  have h_y_i : y i = z i + 1 := by
    dsimp [y]
    have h1 : i ≠ x₀Index := by
      intro heq
      dsimp [auxDictionary, slackDictionary] at hbasis
      rw [Finset.mem_filter] at hbasis
      have : i.val = n := by rw [heq, x₀Index]; rfl
      linarith
    have h2 : n + 1 ≤ i.val := by
      dsimp [auxDictionary, slackDictionary] at hbasis
      rw [Finset.mem_filter] at hbasis
      exact hbasis.2
    simp [h1, h2]
  rw [h_y_i, hz_i]
  have Hsum : (∑ j ∈ (auxDictionary A b).basisᶜ, (auxDictionary A b).coeff i j * y j) =
      (∑ j ∈ (auxDictionary A b).basisᶜ, (auxDictionary A b).coeff i j * z j) + 1 := by
    have H2 : ∀ j ∈ (auxDictionary A b).basisᶜ, (auxDictionary A b).coeff i j * y j =
        (auxDictionary A b).coeff i j * z j + if j = x₀Index then 1 else 0 := by
      intro j hj
      dsimp [auxDictionary, slackDictionary] at hj
      rw [Finset.mem_compl, Finset.mem_filter, not_and, not_le] at hj
      have hj_cast := hj (Finset.mem_univ j)
      dsimp [y]
      have hnot_n1 : ¬(n + 1 ≤ j.val) := by linarith
      by_cases hx0 : j = x₀Index
      · have h_coeff : (auxDictionary A b).coeff i j = 1 := by
          dsimp [auxDictionary, slackDictionary, Dictionary.coeff, Fin.append]
          have hi_cast : n + 1 ≤ i.val := by
            dsimp [auxDictionary, slackDictionary] at hbasis
            rw [Finset.mem_filter] at hbasis
            exact hbasis.2
          have hi_lt : i.val - (n + 1) < m := by
            have : i.val < n + 1 + m := i.isLt
            omega
          have h_eq : i = Fin.natAdd (n + 1) ⟨i.val - (n + 1), hi_lt⟩ := by
            ext; dsimp [Fin.natAdd]; omega
          have h_eq_j : j = Fin.castAdd m ⟨j.val, hj_cast⟩ := by
            ext; rfl
          rw [h_eq, Fin.addCases_right]
          rw [h_eq_j, Fin.addCases_left]
          dsimp [auxMatrix]
          have hnot_j_n : ¬(j.val < n) := by
            intro h
            have : j.val = n := by rw [hx0, x₀Index]; rfl
            omega
          rw [dif_neg hnot_j_n]
          ring
        rw [h_coeff]
        simp [hx0]
      · simp [hx0, hnot_n1]
    rw [Finset.sum_congr rfl H2, Finset.sum_add_distrib]
    congr 1
    have hx0_lt : (x₀Index : Fin (n + 1 + m)).val < n + 1 := by
      dsimp [x₀Index]
      omega
    have hmem : x₀Index ∈ (auxDictionary A b).basisᶜ := by
      dsimp [auxDictionary, slackDictionary]
      rw [Finset.mem_compl, Finset.mem_filter, not_and, not_le]
      intro _
      exact hx0_lt
    rw [Finset.sum_eq_single x₀Index]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hnot
      exfalso
      exact hnot hmem
  rw [Hsum]
  ring

lemma exists_coeff_ne_zero (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (D : Dictionary (Fin (n + 1 + m)) K)
    (hequiv : (auxDictionary A b).Equivalent D) (hzero : D.objConst = 0)
    (hx0 : x₀Index ∈ D.basis) :
    ∃ j ∈ D.basisᶜ, D.coeff x₀Index j ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hz : (auxDictionary A b).IsSolution D.basicSolution :=
    hequiv.isSolution_iff D.basicSolution |>.mpr D.isSolution_basicSolution
  set y := fun j => D.basicSolution j + if j = x₀Index then (1 : K) else if n + 1 ≤ j.val then 1 else 0
  have hy : (auxDictionary A b).IsSolution y := aux_shift_solution A b D.basicSolution hz
  have hyD : D.IsSolution y := hequiv.isSolution_iff y |>.mp hy
  have hy_x0_D := hyD x₀Index hx0
  have Hsum : (∑ j ∈ D.basisᶜ, D.coeff x₀Index j * y j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j hj, zero_mul]
  rw [Hsum, hzero_of_basis A b D hequiv hzero hx0, add_zero] at hy_x0_D
  have hy_x0_def : y x₀Index = D.basicSolution x₀Index + 1 := by
    dsimp [y]
    simp
  have hz_x0 : D.basicSolution x₀Index = 0 := by
    dsimp [Dictionary.basicSolution]
    rw [if_pos hx0, hzero_of_basis A b D hequiv hzero hx0]
  rw [hz_x0, zero_add] at hy_x0_def
  rw [hy_x0_def] at hy_x0_D
  exact one_ne_zero hy_x0_D



lemma forcePivotX₀_equivalent (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (D : Dictionary (Fin (n + 1 + m)) K)
    (hequiv : (auxDictionary A b).Equivalent D) (hzero : D.objConst = 0) :
    let D' := forcePivotX₀ D
    x₀Index ∉ D'.basis ∧ (auxDictionary A b).Equivalent D' := by
  dsimp [forcePivotX₀]
  split_ifs with hx0
  · have hex := exists_coeff_ne_zero A b D hequiv hzero hx0
    have h_nonempty : (D.basisᶜ.filter (fun j => D.coeff x₀Index j ≠ 0)).Nonempty := by
      rcases hex with ⟨j, hj_basis, hj_coeff⟩
      use j
      rw [Finset.mem_filter]
      exact ⟨hj_basis, hj_coeff⟩
    dsimp [minOpt]
    rw [dif_pos h_nonempty]
    set j := (D.basisᶜ.filter (fun j => D.coeff x₀Index j ≠ 0)).min' h_nonempty
    have hj_mem : j ∈ D.basisᶜ.filter (fun j => D.coeff x₀Index j ≠ 0) := Finset.min'_mem _ _
    rw [Finset.mem_filter, Finset.mem_compl] at hj_mem
    have h_not_in_basis : x₀Index ∉ (D.pivot x₀Index j).basis := by
      rw [Dictionary.pivot_basis]
      simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, or_false]
      exact ne_of_mem_of_not_mem hx0 hj_mem.1
    have h_equiv_pivot : D.Equivalent (D.pivot x₀Index j) := Dictionary.equivalent_pivot D hx0 hj_mem.1 hj_mem.2
    exact ⟨h_not_in_basis, Equivalent.trans hequiv h_equiv_pivot⟩
  · exact ⟨hx0, hequiv⟩


lemma forcePivotX₀_feasible (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (D : Dictionary (Fin (n + 1 + m)) K)
    (hequiv : (auxDictionary A b).Equivalent D) (hzero : D.objConst = 0) (hfeas : D.Feasible) :
    (forcePivotX₀ D).Feasible := by
  dsimp [forcePivotX₀]
  split_ifs with hx0
  · intro i hi
    set j := (D.basisᶜ.filter (fun j => D.coeff x₀Index j ≠ 0)).min' (by
      rcases exists_coeff_ne_zero A b D hequiv hzero hx0 with ⟨j', hj'⟩
      use j'
      rw [Finset.mem_filter]
      exact hj')
    have h_nonempty : (D.basisᶜ.filter (fun j => D.coeff x₀Index j ≠ 0)).Nonempty := by
      rcases exists_coeff_ne_zero A b D hequiv hzero hx0 with ⟨j', hj'⟩
      use j'
      rw [Finset.mem_filter]
      exact hj'
    dsimp [minOpt]
    rw [dif_pos h_nonempty]
    have h_rhs_x0 : D.rhs x₀Index = 0 := hzero_of_basis A b D hequiv hzero hx0
    dsimp [Dictionary.pivot] at hi ⊢
    rw [h_rhs_x0]
    simp only [neg_zero, zero_div, mul_zero, sub_zero]
    split_ifs with h1 h2
    · exact le_refl 0
    · exact hfeas i h2.1
    · exact le_refl 0
  · exact hfeas








lemma skip_unskip (i : Fin (n + 1 + m)) (hi : i ≠ x₀Index) : skipX₀ (unskipX₀ i hi) = i := by
  dsimp only [unskipX₀]
  have hi_val : i.val ≠ n := by intro heq; apply hi; apply Fin.ext; exact heq
  split_ifs with h1
  · dsimp only [skipX₀]
    split_ifs
    · apply Fin.ext; exact rfl
  · dsimp only [skipX₀]
    split_ifs with h2
    · exfalso
      have h2' : i.val - 1 < n := h2
      clear hi
      omega
    · apply Fin.ext
      change i.val - 1 + 1 = i.val
      clear hi
      omega

lemma unskip_skip (i : Fin (n + m)) : unskipX₀ (skipX₀ i) (by
    intro h
    have h' := congrArg Fin.val h
    change (skipX₀ i).val = n at h'
    dsimp [skipX₀] at h'
    split_ifs at h'
    · change i.val = n at h'
      omega
    · change i.val + 1 = n at h'
      omega
  ) = i := by
  dsimp only [skipX₀]
  split_ifs with h1
  · dsimp only [unskipX₀]
    split_ifs
    · apply Fin.ext; rfl
  · dsimp only [unskipX₀]
    split_ifs with h2
    · exfalso
      have h2' : i.val + 1 < n := h2
      omega
    · apply Fin.ext
      change i.val + 1 - 1 = i.val
      omega

lemma skip_ne_x0 (j : Fin (n + m)) : skipX₀ j ≠ x₀Index := by
  intro heq
  have heq' := congrArg Fin.val heq
  change (skipX₀ j).val = n at heq'
  dsimp [skipX₀] at heq'
  split_ifs at heq'
  · change j.val = n at heq'
    omega
  · change j.val + 1 = n at heq'
    omega

lemma drop_basis_iff (c : Fin n → K) (D'' : Dictionary (Fin (n + 1 + m)) K) (j : Fin (n + m)) :
    j ∈ (dropX₀ D'' c).basis ↔ skipX₀ j ∈ D''.basis := by
  dsimp [dropX₀]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, h_eq⟩
    have hi_mem := Finset.mem_of_mem_erase i.prop
    rw [← h_eq]
    have H_skip := skip_unskip i.val (Finset.ne_of_mem_erase i.prop)
    rw [H_skip]
    exact hi_mem
  · intro h
    have h_ne : skipX₀ j ≠ x₀Index := skip_ne_x0 j
    use ⟨skipX₀ j, Finset.mem_erase_of_ne_of_mem h_ne h⟩
    constructor
    · apply Finset.mem_attach
    · apply unskip_skip

lemma skipX₀_inj {i j : Fin (n + m)} (h : skipX₀ i = skipX₀ j) : i = j := by
  have h2 : (skipX₀ i).val = (skipX₀ j).val := congrArg Fin.val h
  unfold skipX₀ at h2
  split_ifs at h2
  · ext; exact h2
  · change i.val = j.val + 1 at h2; ext; omega
  · change i.val + 1 = j.val at h2; ext; omega
  · change i.val + 1 = j.val + 1 at h2; ext; omega

lemma dropX₀_feasible (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
    (D'' : Dictionary (Fin (n + 1 + m)) K)
    (hfeas : D''.Feasible) (hx0 : x₀Index ∉ D''.basis) :
    (dropX₀ D'' c).Feasible := by
  intro i hi
  dsimp [dropX₀] at hi ⊢
  rw [Finset.mem_image] at hi
  rcases hi with ⟨j, hj, hj_eq⟩
  have hj_mem : j.val ∈ D''.basis := Finset.mem_of_mem_erase j.prop
  have H_skip : skipX₀ i = j.val := by
    rw [← hj_eq, skip_unskip j.val (Finset.ne_of_mem_erase j.prop)]
  rw [H_skip]
  exact hfeas j.val hj_mem

lemma skipX₀_rhs_eq (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) (i : Fin (n + m)) (hi : i ∈ (slackDictionary A b c).basis) :
    (auxDictionary A b).rhs (skipX₀ i) = (slackDictionary A b c).rhs i := by
  dsimp [auxDictionary, slackDictionary, Dictionary.rhs, x₀Index]
  unfold Fin.append Fin.addCases
  have hi_n : ¬(i.val < n) := by
    dsimp [slackDictionary, Dictionary.basis] at hi
    rw [Finset.mem_filter] at hi
    omega
  have hval : (skipX₀ i).val = i.val + 1 := by unfold skipX₀; simp only [hi_n, dite_false]
  have hi_n_skip : ¬((skipX₀ i).val < n + 1) := by omega
  simp only [hi_n, hi_n_skip, dite_false, eq_rec_constant]
  apply congrArg
  apply Fin.ext
  simp
  omega

lemma skipX₀_coeff_eq (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) (i j : Fin (n + m)) (hi : i ∈ (slackDictionary A b c).basis) (hj : j ∉ (slackDictionary A b c).basis) :
    (auxDictionary A b).coeff (skipX₀ i) (skipX₀ j) = (slackDictionary A b c).coeff i j := by
  dsimp [auxDictionary, slackDictionary, Dictionary.coeff, x₀Index]
  unfold Fin.append Fin.addCases
  have hi_n : ¬(i.val < n) := by
    dsimp [slackDictionary, Dictionary.basis] at hi
    rw [Finset.mem_filter] at hi
    omega
  have hval_i : (skipX₀ i).val = i.val + 1 := by unfold skipX₀; simp only [hi_n, dite_false]
  have hi_n_skip : ¬((skipX₀ i).val < n + 1) := by omega
  have hj_n : j.val < n := by
    dsimp [slackDictionary, Dictionary.basis] at hj
    rw [Finset.mem_filter, not_and, not_le] at hj
    apply hj; simp
  have hval_j : (skipX₀ j).val = j.val := by unfold skipX₀; simp only [hj_n, dite_true]
  have hj_n_skip : (skipX₀ j).val < n + 1 := by omega
  simp only [hi_n, hi_n_skip, dite_false, eq_rec_constant]
  dsimp [auxMatrix]
  have hj_n_skip' : (skipX₀ j).val < n := by omega
  simp only [hj_n, hj_n_skip, hj_n_skip', dite_true, neg_inj, eq_rec_constant]
  congr 1
  · ext; simp; omega
  · ext; simp; omega


lemma aux_slack_isSolution (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) (x : Fin (n + m) → K) :
    (auxDictionary A b).IsSolution (fun i => if hi : i = x₀Index then 0 else x (unskipX₀ i hi)) ↔ (slackDictionary A b c).IsSolution x := by
  change (slackDictionary (auxMatrix A) b auxObj).IsSolution _ ↔ (slackDictionary A b c).IsSolution x
  rw [isSolution_slackDictionary_iff, isSolution_slackDictionary_iff]
  apply forall_congr'
  intro i
  have hsum : ∑ j : Fin (n + 1), auxMatrix A i j * (if hi : Fin.castAdd m j = x₀Index then 0 else x (unskipX₀ (Fin.castAdd m j) hi)) = ∑ j : Fin n, A i j * x (Fin.castAdd m j) := by
    rw [Fin.sum_univ_castSucc]
    have h_last : auxMatrix A i (Fin.last n) * (if hi : Fin.castAdd m (Fin.last n) = x₀Index then 0 else x (unskipX₀ (Fin.castAdd m (Fin.last n)) hi)) = 0 := by
      have h1 : Fin.castAdd m (Fin.last n) = x₀Index := rfl
      have h2 : (if hi : Fin.castAdd m (Fin.last n) = x₀Index then 0 else x (unskipX₀ (Fin.castAdd m (Fin.last n)) hi)) = 0 := by
        rw [h1]
        rw [dif_pos rfl]
      rw [h2, mul_zero]
    rw [h_last, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    have h_mat : auxMatrix A i (Fin.castSucc j) = A i j := by
      change (if hj : j.castSucc.val < n then A i ⟨j.castSucc.val, hj⟩ else -1) = A i j
      have hj : j.castSucc.val < n := j.isLt
      rw [dif_pos hj]
      rfl
    rw [h_mat]
    have h_y : (if hi : Fin.castAdd m (Fin.castSucc j) = x₀Index then 0 else x (unskipX₀ (Fin.castAdd m (Fin.castSucc j)) hi)) = x (Fin.castAdd m j) := by
      have h_ne : Fin.castAdd m (Fin.castSucc j) ≠ x₀Index := by
        intro heq
        have h_val := congrArg Fin.val heq
        change j.val = n at h_val
        omega
      rw [dif_neg h_ne]
      congr 1
      apply Fin.ext
      change (unskipX₀ (Fin.castAdd m (Fin.castSucc j)) h_ne).val = (Fin.castAdd m j).val
      unfold unskipX₀
      split_ifs with h_lt
      · rfl
      · exfalso
        have h1 : (Fin.castAdd m (Fin.castSucc j)).val = j.val := rfl
        have h2 : j.val < n := j.isLt
        omega
    rw [h_y]
  have hy_nat : (if hi : Fin.natAdd (n + 1) i = x₀Index then 0 else x (unskipX₀ (Fin.natAdd (n + 1) i) hi)) = x (Fin.natAdd n i) := by
    have hne : Fin.natAdd (n + 1) i ≠ x₀Index := by
      intro heq
      have := congrArg Fin.val heq
      change n + 1 + i.val = n at this
      omega
    rw [dif_neg hne]
    congr 1
    apply Fin.ext
    change (unskipX₀ _ _).val = (Fin.natAdd n i).val
    unfold unskipX₀
    split_ifs with h_lt
    · exfalso
      have h1 : (Fin.natAdd (n + 1) i).val = n + 1 + i.val := rfl
      omega
    · have h2 : (Fin.natAdd (n + 1) i).val = n + 1 + i.val := rfl
      have h3 : (Fin.natAdd n i).val = n + i.val := rfl
      change (Fin.natAdd (n + 1) i).val - 1 = (Fin.natAdd n i).val
      omega
  rw [hy_nat, hsum]


lemma dropX₀_equiv (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
    (D'' : Dictionary (Fin (n + 1 + m)) K)
    (h_D''_equiv : (auxDictionary A b).Equivalent D'')
    (h_D''_not_x0 : x₀Index ∉ D''.basis)
    (hfeas : D''.Feasible) :
    (dropX₀ D'' c).Equivalent (slackDictionary A b c) := by
  constructor
  · intro x
    set y : Fin (n + 1 + m) → K := fun i => if hi : i = x₀Index then 0 else x (unskipX₀ i hi)
    have hy_skip : ∀ j, y (skipX₀ j) = x j := by
      intro j; dsimp [y]; have hj : skipX₀ j ≠ x₀Index := skip_ne_x0 j
      simp only [hj, dite_false]; exact congrArg x (unskip_skip j)
    have hyx0 : y x₀Index = 0 := by dsimp [y]; simp only [dite_true]
    have H_sum : ∀ i' : Fin (n + m), ∑ j ∈ (dropX₀ D'' c).basisᶜ, (dropX₀ D'' c).coeff i' j * x j =
      ∑ j ∈ D''.basisᶜ, D''.coeff (skipX₀ i') j * y j := by
      intro i'
      have H_bij : ∑ j ∈ D''.basisᶜ.erase x₀Index, D''.coeff (skipX₀ i') j * y j + D''.coeff (skipX₀ i') x₀Index * y x₀Index = 
        ∑ j ∈ D''.basisᶜ, D''.coeff (skipX₀ i') j * y j := by
        apply Finset.sum_erase_add _ _ (Finset.mem_compl.2 h_D''_not_x0)
      rw [← H_bij, hyx0, mul_zero, add_zero]
      have H_image : D''.basisᶜ.erase x₀Index = Finset.image skipX₀ (dropX₀ D'' c).basisᶜ := by
        ext j
        simp only [Finset.mem_erase, Finset.mem_compl, Finset.mem_image]
        constructor
        · rintro ⟨hj1, hj2⟩
          use unskipX₀ j hj1
          constructor
          · intro hc
            have hc' := (drop_basis_iff c D'' (unskipX₀ j hj1)).mp hc
            rw [skip_unskip] at hc'
            exact hj2 hc'
          · exact skip_unskip j hj1
        · rintro ⟨j', hj1, hj2⟩
          rw [← hj2]
          constructor
          · exact skip_ne_x0 j'
          · intro hc
            apply hj1
            exact (drop_basis_iff c D'' j').mpr hc
      rw [H_image, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j _
        dsimp [dropX₀]
        rw [hy_skip]
      · intro a _ b _ h_eq
        exact skipX₀_inj h_eq
    
    have h_drop : (dropX₀ D'' c).IsSolution x ↔ D''.IsSolution y := by
      dsimp [IsSolution]
      constructor
      · intro h i hi
        by_cases hi_x0 : i = x₀Index
        · rw [hi_x0] at hi
          exfalso
          exact h_D''_not_x0 hi
        · have hi_unskip : unskipX₀ i hi_x0 ∈ (dropX₀ D'' c).basis := by
            apply (drop_basis_iff c D'' (unskipX₀ i hi_x0)).mpr
            rw [skip_unskip]
            exact hi
          have H_i := h (unskipX₀ i hi_x0) hi_unskip
          have H_sum_aux : ∑ j ∈ (dropX₀ D'' c).basisᶜ, (dropX₀ D'' c).coeff (unskipX₀ i hi_x0) j * x j = 
            ∑ j ∈ D''.basisᶜ, D''.coeff i j * y j := by
            have h_sum := H_sum (unskipX₀ i hi_x0)
            rw [skip_unskip] at h_sum
            exact h_sum
          rw [H_sum_aux] at H_i
          have H_rhs : (dropX₀ D'' c).rhs (unskipX₀ i hi_x0) = D''.rhs i := by
            dsimp [dropX₀]
            rw [skip_unskip]
          rw [H_rhs] at H_i
          rw [← H_i]
          dsimp [y]
          simp only [hi_x0, dite_false]
      · intro h i' hi'
        have hi_skip : skipX₀ i' ∈ D''.basis := by
          apply (drop_basis_iff c D'' i').mp
          exact hi'
        have H_i' := h (skipX₀ i') hi_skip
        have H_sum_aux : ∑ j ∈ D''.basisᶜ, D''.coeff (skipX₀ i') j * y j = 
          ∑ j ∈ (dropX₀ D'' c).basisᶜ, (dropX₀ D'' c).coeff i' j * x j := by
          exact (H_sum i').symm
        rw [H_sum_aux] at H_i'
        have H_rhs : D''.rhs (skipX₀ i') = (dropX₀ D'' c).rhs i' := by
          dsimp [dropX₀]
        rw [H_rhs] at H_i'
        rw [hy_skip] at H_i'
        exact H_i'
    rw [h_drop]
    rw [← aux_slack_isSolution A b c x]
    exact (h_D''_equiv.isSolution_iff _).symm
  
  · intro x hx
    have hLHS : (dropX₀ D'' c).value x = ∑ j : Fin n, c j * x (Fin.castAdd m j) := by
      dsimp [Dictionary.value, dropX₀, Dictionary.objConst, Dictionary.objCoeff]
      change (∑ j : Fin n, if skipX₀ (Fin.castAdd m j) ∈ D''.basis then c j * D''.rhs (skipX₀ (Fin.castAdd m j)) else 0) +
        ∑ j ∈ (dropX₀ D'' c).basisᶜ, ((if hk : j.val < n then c ⟨j.val, hk⟩ else 0) + ∑ j_1 : Fin n, if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) else 0) * x j =
        ∑ j : Fin n, c j * x (Fin.castAdd m j)
      have H_distrib : ∀ j ∈ (dropX₀ D'' c).basisᶜ, ((if hk : j.val < n then c ⟨j.val, hk⟩ else 0) + ∑ j_1 : Fin n, if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) else 0) * x j =
        (if hk : j.val < n then c ⟨j.val, hk⟩ else 0) * x j + (∑ j_1 : Fin n, if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) else 0) * x j := by
        intro j _
        ring
      rw [Finset.sum_congr rfl H_distrib, Finset.sum_add_distrib]
      have h1 : ∀ j ∈ (dropX₀ D'' c).basisᶜ, (∑ j_1 : Fin n, if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) else 0) * x j =
        ∑ j_1 : Fin n, (if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) else 0) * x j := by
        intro j _
        rw [Finset.sum_mul]
      rw [Finset.sum_congr rfl h1]
      have H_sum_comm : ∑ j ∈ (dropX₀ D'' c).basisᶜ, ∑ j_1 : Fin n, (if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) else 0) * x j =
        ∑ j_1 : Fin n, (if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * ∑ j ∈ (dropX₀ D'' c).basisᶜ, D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) * x j else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j_1 _
        split_ifs with h_skip
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        · rw [Finset.sum_eq_zero]
          intro j _
          ring
      rw [H_sum_comm]
      have H_sum_combine : (∑ j : Fin n, if skipX₀ (Fin.castAdd m j) ∈ D''.basis then c j * D''.rhs (skipX₀ (Fin.castAdd m j)) else 0) +
        ∑ j_1 : Fin n, (if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * ∑ j ∈ (dropX₀ D'' c).basisᶜ, D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) * x j else 0) =
        ∑ j : Fin n, if skipX₀ (Fin.castAdd m j) ∈ D''.basis then c j * x (Fin.castAdd m j) else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with h_skip
        · rw [← mul_add]
          congr 1
          have hx_j : x (Fin.castAdd m j) = D''.rhs (skipX₀ (Fin.castAdd m j)) + ∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, D''.coeff (skipX₀ (Fin.castAdd m j)) (skipX₀ x_1) * x x_1 := hx (Fin.castAdd m j) ((drop_basis_iff c D'' (Fin.castAdd m j)).mpr h_skip)
          exact hx_j.symm
        · exact add_zero 0
      have h_assoc : (∑ j : Fin n, if skipX₀ (Fin.castAdd m j) ∈ D''.basis then c j * D''.rhs (skipX₀ (Fin.castAdd m j)) else 0) +
        (∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ else 0) * x x_1 +
          ∑ j_1 : Fin n, (if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * ∑ j ∈ (dropX₀ D'' c).basisᶜ, D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) * x j else 0)) =
        ((∑ j : Fin n, if skipX₀ (Fin.castAdd m j) ∈ D''.basis then c j * D''.rhs (skipX₀ (Fin.castAdd m j)) else 0) +
        ∑ j_1 : Fin n, (if skipX₀ (Fin.castAdd m j_1) ∈ D''.basis then c j_1 * ∑ j ∈ (dropX₀ D'' c).basisᶜ, D''.coeff (skipX₀ (Fin.castAdd m j_1)) (skipX₀ j) * x j else 0)) +
        ∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ else 0) * x x_1 := by
        rw [← add_assoc, add_right_comm]
      rw [h_assoc]
      rw [H_sum_combine]
      have h_split : ∑ j : Fin n, c j * x (Fin.castAdd m j) =
        (∑ j : Fin n, if skipX₀ (Fin.castAdd m j) ∈ D''.basis then c j * x (Fin.castAdd m j) else 0) +
        (∑ j : Fin n, if skipX₀ (Fin.castAdd m j) ∉ D''.basis then c j * x (Fin.castAdd m j) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : skipX₀ (Fin.castAdd m j) ∈ D''.basis
        · rw [if_pos h, if_neg (not_not.mpr h)]
          ring
        · rw [if_neg h, if_pos h]
          ring
      rw [h_split]
      congr 1
      have h_distrib_if : ∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ else 0) * x x_1 =
        ∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0 := by
        apply Finset.sum_congr rfl
        intro x_1 _
        by_cases hk : x_1.val < n
        · have H1 : (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ else 0) = c ⟨x_1.val, hk⟩ := dif_pos hk
          have H2 : (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) = c ⟨x_1.val, hk⟩ * x x_1 := dif_pos hk
          rw [H1, H2]
        · have H1 : (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ else 0) = 0 := dif_neg hk
          have H2 : (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) = 0 := dif_neg hk
          rw [H1, H2, zero_mul]
      rw [h_distrib_if]
  
      have h_image : ∑ j : Fin n, (if skipX₀ (Fin.castAdd m j) ∉ D''.basis then c j * x (Fin.castAdd m j) else 0) =
        ∑ x_1 ∈ Finset.image (Fin.castAdd m) Finset.univ, if skipX₀ x_1 ∉ D''.basis then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0 := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro j _
          have hk : (Fin.castAdd m j).val < n := j.isLt
          have heq : (⟨(Fin.castAdd m j).val, hk⟩ : Fin n) = j := by apply Fin.ext; rfl
          by_cases h1 : skipX₀ (Fin.castAdd m j) ∈ D''.basis
          · have H1 : (if skipX₀ (Fin.castAdd m j) ∉ D''.basis then c j * x (Fin.castAdd m j) else 0) = 0 := if_neg (not_not.mpr h1)
            have H2 : (if skipX₀ (Fin.castAdd m j) ∉ D''.basis then (if hk : (Fin.castAdd m j).val < n then c ⟨(Fin.castAdd m j).val, hk⟩ * x (Fin.castAdd m j) else 0) else 0) = 0 := if_neg (not_not.mpr h1)
            rw [H1, H2]
          · have H1 : (if skipX₀ (Fin.castAdd m j) ∉ D''.basis then c j * x (Fin.castAdd m j) else 0) = c j * x (Fin.castAdd m j) := if_pos h1
            have H2 : (if skipX₀ (Fin.castAdd m j) ∉ D''.basis then (if hk : (Fin.castAdd m j).val < n then c ⟨(Fin.castAdd m j).val, hk⟩ * x (Fin.castAdd m j) else 0) else 0) = (if hk : (Fin.castAdd m j).val < n then c ⟨(Fin.castAdd m j).val, hk⟩ * x (Fin.castAdd m j) else 0) := if_pos h1
            have H3 : (if hk : (Fin.castAdd m j).val < n then c ⟨(Fin.castAdd m j).val, hk⟩ * x (Fin.castAdd m j) else 0) = c ⟨(Fin.castAdd m j).val, hk⟩ * x (Fin.castAdd m j) := dif_pos hk
            rw [H1, H2, H3, heq]
        · intro a _ b _ hab
          apply Fin.ext
          have hval : (Fin.castAdd m a).val = (Fin.castAdd m b).val := by rw [hab]
          exact hval
      rw [h_image]
  
      have H_LHS : ∑ x_1 ∈ Finset.image (Fin.castAdd m) (Finset.univ : Finset (Fin n)), (if skipX₀ x_1 ∉ D''.basis then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) =
        ∑ x_1 : Fin (n + m), (if skipX₀ x_1 ∉ D''.basis then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) := by
        apply Finset.sum_subset
        · intro _ _
          exact Finset.mem_univ _
        · intro x_1 _ hx
          have h_not_lt : ¬(x_1.val < n) := by
            by_contra h_lt
            have h_in : x_1 ∈ Finset.image (Fin.castAdd m) (Finset.univ : Finset (Fin n)) := by
              rw [Finset.mem_image]
              use ⟨x_1.val, h_lt⟩
              constructor
              · exact Finset.mem_univ _
              · apply Fin.ext; rfl
            exact hx h_in
          by_cases h1 : skipX₀ x_1 ∈ D''.basis
          · exact if_neg (not_not.mpr h1)
          · have H1 : (if skipX₀ x_1 ∉ D''.basis then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) = (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) := if_pos h1
            have H2 : (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) = 0 := dif_neg h_not_lt
            rw [H1, H2]
  
      have H_RHS : ∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) =
        ∑ x_1 : Fin (n + m), (if skipX₀ x_1 ∉ D''.basis then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) := by
        have h1 : ∑ x_1 : Fin (n + m), (if skipX₀ x_1 ∉ D''.basis then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) =
          ∑ x_1 : Fin (n + m), (if x_1 ∈ (dropX₀ D'' c).basisᶜ then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro x_1 _
          by_cases h_basis : skipX₀ x_1 ∈ D''.basis
          · have h1_1 : x_1 ∉ (dropX₀ D'' c).basisᶜ := by
              rw [Finset.mem_compl]
              intro h
              rw [drop_basis_iff] at h
              exact h h_basis
            have H1 : (if skipX₀ x_1 ∉ D''.basis then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) = 0 := if_neg (not_not.mpr h_basis)
            have H2 : (if x_1 ∈ (dropX₀ D'' c).basisᶜ then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) = 0 := if_neg h1_1
            rw [H1, H2]
          · have h2_1 : x_1 ∈ (dropX₀ D'' c).basisᶜ := by
              rw [Finset.mem_compl]
              intro h
              rw [drop_basis_iff] at h
              exact h_basis h
            have H1 : (if skipX₀ x_1 ∉ D''.basis then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) = (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) := if_pos h_basis
            have H2 : (if x_1 ∈ (dropX₀ D'' c).basisᶜ then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) = (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) := if_pos h2_1
            rw [H1, H2]
        
        have h2 : ∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) =
          ∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, (if x_1 ∈ (dropX₀ D'' c).basisᶜ then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro x_1 hx_1
          exact (if_pos hx_1).symm
          
        have h3 : ∑ x_1 ∈ (dropX₀ D'' c).basisᶜ, (if x_1 ∈ (dropX₀ D'' c).basisᶜ then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) =
          ∑ x_1 : Fin (n + m), (if x_1 ∈ (dropX₀ D'' c).basisᶜ then (if hk : x_1.val < n then c ⟨x_1.val, hk⟩ * x x_1 else 0) else 0) := by
          apply Finset.sum_subset
          · intro _ _
            exact Finset.mem_univ _
          · intro x_1 _ hx
            exact if_neg hx
            
        rw [h2, h3, ← h1]
        
      rw [H_LHS, H_RHS]
    
    have hRHS : (slackDictionary A b c).value x = ∑ j : Fin n, c j * x (Fin.castAdd m j) := by
      dsimp [Dictionary.value, slackDictionary, Dictionary.objConst, Dictionary.objCoeff]
      rw [zero_add]
      have h_eq_set : (Finset.filter (fun j : Fin (n + m) => n ≤ j.val) Finset.univ)ᶜ = Finset.image (Fin.castAdd m) Finset.univ := by
        ext j
        simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le, Finset.mem_image]
        constructor
        · intro hj
          use ⟨j.val, hj⟩
          rfl
        · rintro ⟨j', hj2⟩
          rw [← hj2]
          exact j'.isLt
      rw [h_eq_set, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j _
        have h_add : Fin.append c 0 (Fin.castAdd m j) = c j := by
          dsimp [Fin.append, Fin.addCases]
          have hj : j.val < n := j.isLt
          rw [dif_pos hj]
        rw [h_add]
      · intro a _ b _ hab
        apply Fin.ext
        have hval : (Fin.castAdd m a).val = (Fin.castAdd m b).val := by rw [hab]
        exact hval
  
    exact hLHS.trans hRHS.symm

theorem dropX₀_equivalent (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)
    (D : Dictionary (Fin (n + 1 + m)) K)
    (hopt : (phaseOneDict A b).simplex = .optimal D)
    (hzero : D.objConst = 0) :
    let D' := dropX₀ (forcePivotX₀ D) c;
    D'.Feasible ∧ D'.Equivalent (slackDictionary A b c) := by
  have hequiv : (phaseOneDict A b).Equivalent (auxDictionary A b) := phaseOneDict_equivalent A b
  have hfeas_phase1 := phaseOneDict_feasible A b
  obtain ⟨hequiv2, hfeas2, hopt2⟩ := Dictionary.run_eq_optimal (phaseOneDict A b) hfeas_phase1 hopt
  have hfeas : D.Feasible := hfeas2
  have hequiv_aux : (auxDictionary A b).Equivalent D := hequiv.symm.trans hequiv2
  have h_D''_equiv : (auxDictionary A b).Equivalent (forcePivotX₀ D) := (forcePivotX₀_equivalent A b D hequiv_aux hzero).2
  have h_D''_not_x0 : x₀Index ∉ (forcePivotX₀ D).basis := (forcePivotX₀_equivalent A b D hequiv_aux hzero).1
  have hfeas'' : (forcePivotX₀ D).Feasible := forcePivotX₀_feasible A b D hequiv_aux hzero hfeas
  exact ⟨dropX₀_feasible A b c (forcePivotX₀ D) hfeas'' h_D''_not_x0, dropX₀_equiv A b c (forcePivotX₀ D) h_D''_equiv h_D''_not_x0 hfeas''⟩

/-- The total certificate specification for the two-phase simplex method. -/
theorem twoPhase_spec (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) :
    match twoPhase A b c with
    | TwoPhaseResult.infeasible y => 0 ≤ y ∧ 0 ≤ y ᵥ* A ∧ y ⬝ᵥ b < 0
    | TwoPhaseResult.unbounded x d => 0 ≤ x ∧ A *ᵥ x ≤ b ∧ 0 ≤ d ∧ A *ᵥ d ≤ 0 ∧ 0 < c ⬝ᵥ d
    | TwoPhaseResult.optimal x y => 0 ≤ x ∧ A *ᵥ x ≤ b ∧ 0 ≤ y ∧ c ≤ y ᵥ* A ∧ c ⬝ᵥ x = y ⬝ᵥ b := sorry

end Cslib.Algorithms.Lean.Simplex
