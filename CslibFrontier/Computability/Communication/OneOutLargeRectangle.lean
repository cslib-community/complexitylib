/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.OneOutRectangle
public import CslibFrontier.Probability.IID
import CslibFrontier.Computability.Communication.Announce
import CslibFrontier.Probability.IID.Distinct
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.Product.Resample
import Mathlib.Tactic

/-!
# A large solvable rectangle from a one-out protocol

[ChukhinKulikovMihajlinSmal2026], Lemma 5.2 (printed pp. 10–11; PDF pp. 11–12): if a protocol `p`
solves the one-out-of-`k` problem `Relation R` for a total relation `R` on finite types, then for
all distributions `μ` on Alice's inputs and `ν` on Bob's inputs there is a rectangle `A' × B'`,
solved for `R` by a protocol of depth at most `max p.depth ⌈log₂ |Z|⌉`, with
`μ A' + ν B' ≥ 1 + 1 / k²` (`exists_large_solvable_rectangle`).

If some input has mass at least `1 / k²`, a single row or column suffices: the other player
announces a valid answer. Otherwise the proof runs a hybrid argument on independent tuples
`x ∼ μᵏ`, `y ∼ νᵏ`. The hybrid goal `hybridGoal p j x y` judges the leaves announcing a
coordinate below `j` by Alice's tuple and the others by Bob's tuple; `hybrid μ ν p j` is the
probability that Alice can force it. Distinct tuples, which occur with total probability at least
`1 + 1 / k` (`Probability.PMF.iid_injective_pair_ge`), make the last hybrid likely and the first
unlikely, so some step gains `1 / k²` (`exists_hybrid_step`). Redrawing the pivotal coordinate
(`Probability.PMF.sum_pi_mul_update`) writes that step as the average, over the other coordinates,
of `μ A' + ν B' - 1` for the forcing rectangle `aliceSide × bobSide` of
`OneOutRectangle` (`hybrid_succ_sub_hybrid`), and some background attains the average.

The source indexes coordinates from `1`; here `hybridGoal p j` is the source's `L_j` with
coordinates numbered from `0`, so leaves with index `< j` are Alice's. The source's hypothesis
`k ≤ min |A| |B|` is not needed: without distinct tuples some atom is heavy. The source takes `p`
optimal; the statement holds for every protocol `p` solving the one-out relation.

## Main definitions

* `Cslib.Communication.OneOut.hybridGoal`: the hybrid leaf sets `L_j` of the source.
* `Cslib.Communication.OneOut.hybrid`: the probabilities `p_j` that Alice can force them.

## Main results

* `Cslib.Communication.OneOut.exists_hybrid_step`: some hybrid step gains `1 / k²`.
* `Cslib.Communication.OneOut.hybrid_succ_sub_hybrid`: a hybrid step is the average forcing
  rectangle advantage.
* `Cslib.Communication.OneOut.exists_large_forcing_rectangle`: the light-atom case.
* `Cslib.Communication.OneOut.exists_large_solvable_rectangle`: Lemma 5.2.
-/

public section

namespace Cslib.Communication.OneOut

open Protocol Cslib.Probability.PMF Finset

variable {X Y Z : Type*} {k : ℕ}

/-- The source's hybrid leaf set `L_j`: a leaf announcing a coordinate below `j` is judged by
Alice's tuple, which must lie in its projection; any other leaf is judged by Bob's tuple, which
must lie outside its projection. -/
@[expose] def hybridGoal (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)) (j : ℕ)
    (x : Fin k → X) (y : Fin k → Y) (w : Fin p.leafCount) : Prop :=
  if ((p.leafOutput w).index : ℕ) < j then x (p.leafOutput w).index ∈ aliceProjection p w
  else y (p.leafOutput w).index ∉ bobProjection p w

open scoped Classical in
/-- The source's `p_j`: the probability, for independent tuples `x ∼ μᵏ` and `y ∼ νᵏ`, that Alice
can force the hybrid goal `L_j`. The tuples need not be injective. -/
noncomputable def hybrid [Fintype X] [Fintype Y] (μ : PMF X) (ν : PMF Y)
    (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)) (j : ℕ) : ℝ :=
  ∑ x, (iid μ k x).toReal * ∑ y, (iid ν k y).toReal *
    if p.labelLeaves.CanForce true (hybridGoal p j x y) then 1 else 0

variable [Fintype X] [Fintype Y] (μ : PMF X) (ν : PMF Y)
  (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))

/-- Last hybrid: on a distinct tuple, Alice forces `L_k` by following her messages in `p`. -/
theorem toOuterMeasure_injective_le_hybrid :
    ((iid μ k).toOuterMeasure {x | Function.Injective x}).toReal ≤ hybrid μ ν p k := by
  classical
  rw [toOuterMeasure_toReal_eq_sum_ite, hybrid]
  refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  by_cases hx : Function.Injective x
  · have hforce (y : Fin k → Y) : p.labelLeaves.CanForce true (hybridGoal p k x y) :=
      p.labelLeaves.canForce_mono true (fun w hw => by simpa [hybridGoal] using hw)
        (canForce_aliceProjection p ⟨x, hx⟩)
    simp only [Set.mem_ofPred_eq, hx, hforce, ite_true, mul_one, sum_toReal, le_refl]
  · simp only [Set.mem_ofPred_eq, hx, ite_false]
    exact sum_nonneg fun y _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

/-- First hybrid: on a distinct tuple, Bob forces the complement of `L_0` by following his
messages in `p`, so Alice cannot force `L_0` by determinacy. -/
theorem hybrid_zero_le :
    hybrid μ ν p 0 ≤ 1 - ((iid ν k).toOuterMeasure {y | Function.Injective y}).toReal := by
  classical
  have hcompl := toOuterMeasure_toReal_add_compl (iid ν k) {y | Function.Injective y}
  rw [show 1 - ((iid ν k).toOuterMeasure {y | Function.Injective y}).toReal =
    ((iid ν k).toOuterMeasure {y | Function.Injective y}ᶜ).toReal by linarith,
    toOuterMeasure_toReal_eq_sum_ite, hybrid]
  refine sum_mul_le _ _ _ fun x => sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  by_cases hy : Function.Injective y
  · have hgoal : hybridGoal p 0 x y =
        fun w => ¬ y (p.leafOutput w).index ∈ bobProjection p w := by
      funext w
      simp [hybridGoal]
    have hnot : ¬ p.labelLeaves.CanForce true
        (fun w => ¬ y (p.leafOutput w).index ∈ bobProjection p w) := fun h =>
      (p.labelLeaves.canForce_not_iff false _).mp h (canForce_bobProjection p ⟨y, hy⟩)
    simp [hgoal, hnot, hy]
  · simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hy, not_false_eq_true, ite_true]
    split_ifs <;> norm_num

/-- **Telescoping.** If all atoms are light, distinct tuples are likely enough that some hybrid
step increases the forcing probability by at least `1 / k²`. -/
theorem exists_hybrid_step (hk : 0 < k)
    (hμ : ∀ a, (μ a).toReal ≤ ((k : ℝ) ^ 2)⁻¹) (hν : ∀ b, (ν b).toReal ≤ ((k : ℝ) ^ 2)⁻¹) :
    ∃ i : Fin k, ((k : ℝ) ^ 2)⁻¹ ≤ hybrid μ ν p (i + 1) - hybrid μ ν p i := by
  have hpair := iid_injective_pair_ge μ ν k hk hμ hν
  have hlast := toOuterMeasure_injective_le_hybrid μ ν p
  have hfirst := hybrid_zero_le μ ν p
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsum : ∑ _i ∈ range k, ((k : ℝ) ^ 2)⁻¹ ≤
      ∑ i ∈ range k, (hybrid μ ν p (i + 1) - hybrid μ ν p i) := by
    rw [sum_range_sub (hybrid μ ν p), sum_const, card_range, nsmul_eq_mul]
    have : (k : ℝ) * ((k : ℝ) ^ 2)⁻¹ = (k : ℝ)⁻¹ := by field_simp
    linarith
  obtain ⟨i, hi, hle⟩ := exists_le_of_sum_le (nonempty_range_iff.mpr hk.ne') hsum
  exact ⟨⟨i, mem_range.mp hi⟩, hle⟩

/-- The background of a hybrid step: the leaves of other coordinates that `L_{i+1}` contains for
the fixed tuples `x` and `y`. At these leaves `L_i` and `L_{i+1}` agree. -/
@[expose] def stepBackground (i : Fin k) (x : Fin k → X) (y : Fin k → Y) :
    Set (Fin p.leafCount) :=
  {w | hybridGoal p (i + 1) x y w}

omit [Fintype X] [Fintype Y] in
/-- After redrawing coordinate `i` of both tuples, `L_{i+1}` is Alice's pivotal goal. -/
private theorem hybridGoal_succ_update (i : Fin k)
    (x : Fin k → X) (y : Fin k → Y) (a : X) (b : Y) :
    hybridGoal p (i + 1) (Function.update x i a) (Function.update y i b) =
      aliceGoal p i (stepBackground p i x y) a := by
  funext w
  by_cases hw : (p.leafOutput w).index = i
  · simp [hybridGoal, aliceGoal, hw]
  · simp [hybridGoal, aliceGoal, stepBackground, hw]

omit [Fintype X] [Fintype Y] in
/-- After redrawing coordinate `i` of both tuples, `L_i` is the complement of Bob's pivotal goal. -/
private theorem hybridGoal_update (i : Fin k)
    (x : Fin k → X) (y : Fin k → Y) (a : X) (b : Y) :
    hybridGoal p i (Function.update x i a) (Function.update y i b) =
      fun w => ¬ bobGoal p i (stepBackground p i x y) b w := by
  funext w
  by_cases hw : (p.leafOutput w).index = i
  · simp [hybridGoal, bobGoal, hw]
  · have hlt : ((p.leafOutput w).index : ℕ) < i ↔ ((p.leafOutput w).index : ℕ) < i + 1 := by
      have := Fin.val_ne_of_ne hw
      omega
    simp [hybridGoal, bobGoal, stepBackground, hw, hlt]

/-- Redrawing coordinate `i` of both tuples does not change a hybrid probability. -/
private theorem hybrid_eq_sum_update (i : Fin k) (j : ℕ) :
    open scoped Classical in
    hybrid μ ν p j = ∑ x, (iid μ k x).toReal * ∑ y, (iid ν k y).toReal *
      ∑ a, (μ a).toReal * ∑ b, (ν b).toReal *
        if p.labelLeaves.CanForce true
          (hybridGoal p j (Function.update x i a) (Function.update y i b)) then 1 else 0 := by
  classical
  rw [hybrid, iid_eq_pi, iid_eq_pi, sum_pi_mul_update (fun _ => μ) i]
  refine sum_congr rfl fun x _ => congrArg _ ?_
  have h (x' : Fin k → X) :
      ∑ y, (pi (fun _ => ν) y).toReal *
        (if p.labelLeaves.CanForce true (hybridGoal p j x' y) then 1 else 0) =
      ∑ y, (pi (fun _ => ν) y).toReal * ∑ b, (ν b).toReal *
        if p.labelLeaves.CanForce true (hybridGoal p j x' (Function.update y i b)) then 1
        else 0 :=
    sum_pi_mul_update (fun _ => ν) i _
  simp only [h, mul_sum]
  refine sum_comm.trans (sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
    sum_congr rfl fun _ _ => by ring)

/-- **The pivotal step.** A hybrid step is the average, over the tuples outside the pivotal
coordinate, of the advantage `μ A' + ν B' - 1` of the forcing rectangle that those tuples fix. -/
theorem hybrid_succ_sub_hybrid (i : Fin k) :
    hybrid μ ν p (i + 1) - hybrid μ ν p i = ∑ x, (iid μ k x).toReal * ∑ y, (iid ν k y).toReal *
      ((μ.toOuterMeasure (aliceSide p i (stepBackground p i x y))).toReal +
        (ν.toOuterMeasure (bobSide p i (stepBackground p i x y))).toReal - 1) := by
  classical
  rw [hybrid_eq_sum_update μ ν p i, hybrid_eq_sum_update μ ν p i, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_sub, ← sum_sub_distrib]
  refine congrArg _ (sum_congr rfl fun y _ => ?_)
  rw [← mul_sub]
  refine congrArg _ ?_
  have hcompl := toOuterMeasure_toReal_add_compl ν (bobSide p i (stepBackground p i x y))
  simp only [hybridGoal_succ_update, hybridGoal_update, canForce_before_iff]
  rw [toOuterMeasure_toReal_eq_sum_ite, toOuterMeasure_toReal_eq_sum_ite ν (bobSide _ _ _)ᶜ] at *
  have hA : ∑ a, (μ a).toReal * ∑ b, (ν b).toReal *
      (if p.labelLeaves.CanForce true (aliceGoal p i (stepBackground p i x y) a) then 1 else 0) =
      ∑ a, (μ a).toReal * if a ∈ aliceSide p i (stepBackground p i x y) then 1 else 0 := by
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_mul, sum_toReal, one_mul]
    rfl
  have hB : ∑ a, (μ a).toReal * ∑ b, (ν b).toReal *
      (if b ∉ bobSide p i (stepBackground p i x y) then 1 else 0) =
      ∑ b, (ν b).toReal * if b ∈ (bobSide p i (stepBackground p i x y))ᶜ then 1 else 0 := by
    rw [← sum_mul, sum_toReal, one_mul]
    rfl
  rw [hA, hB, toOuterMeasure_toReal_eq_sum_ite ν]
  linarith

omit [Fintype X] [Fintype Y] in
/-- **The light-atom case of Lemma 5.2.** If no atom of `μ` or `ν` has mass above `1 / k²`, some
coordinate and background give a forcing rectangle with `μ A' + ν B' ≥ 1 + 1 / k²`. -/
theorem exists_large_forcing_rectangle [Finite X] [Finite Y] (hk : 0 < k)
    (hμ : ∀ a, (μ a).toReal ≤ ((k : ℝ) ^ 2)⁻¹) (hν : ∀ b, (ν b).toReal ≤ ((k : ℝ) ^ 2)⁻¹) :
    ∃ (i : Fin k) (background : Set (Fin p.leafCount)),
      1 + ((k : ℝ) ^ 2)⁻¹ ≤ (μ.toOuterMeasure (aliceSide p i background)).toReal +
        (ν.toOuterMeasure (bobSide p i background)).toReal := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  obtain ⟨i, hi⟩ := exists_hybrid_step μ ν p hk hμ hν
  rw [hybrid_succ_sub_hybrid] at hi
  obtain ⟨x, -, hx⟩ := exists_mem_support_sum_mul_le (iid μ k) _
  obtain ⟨y, -, hy⟩ := exists_mem_support_sum_mul_le (iid ν k) _
  exact ⟨i, stepBackground p i x y, by linarith [hi.trans (hx.trans hy)]⟩

omit [Fintype X] [Fintype Y] in
/-- **[ChukhinKulikovMihajlinSmal2026], Lemma 5.2.** Let `p` solve the one-out-of-`k` problem for
a total relation `R` on finite types. For all distributions `μ` and `ν` on Alice's and Bob's
inputs, some rectangle `A' × B'` is solved for `R` by a protocol of depth at most
`max p.depth ⌈log₂ |Z|⌉` and has `μ A' + ν B' ≥ 1 + 1 / k²`. -/
theorem exists_large_solvable_rectangle [Finite X] [Finite Y] [Fintype Z] {R : X → Y → Z → Prop}
    (htotal : ∀ x y, ∃ z, R x y z) (hp : p.Solves (Relation R) Set.univ Set.univ) :
    ∃ (A' : Set X) (B' : Set Y) (q : Protocol X Y Z),
      q.depth ≤ max p.depth (Nat.clog 2 (Fintype.card Z)) ∧ q.Solves R A' B' ∧
        1 + ((k : ℝ) ^ 2)⁻¹ ≤ (μ.toOuterMeasure A').toReal + (ν.toOuterMeasure B').toReal := by
  classical
  have hk : 0 < k := (p.leafOutput ⟨0, p.leafCount_pos⟩).index.pos
  obtain ⟨x₀, -⟩ := μ.support_nonempty
  obtain ⟨y₀, -⟩ := ν.support_nonempty
  have : Nonempty Z := ⟨(htotal x₀ y₀).choose⟩
  by_cases hμ : ∃ a, ((k : ℝ) ^ 2)⁻¹ ≤ (μ a).toReal
  · -- A heavy row: Bob announces a valid answer for the fixed input of Alice.
    obtain ⟨a, ha⟩ := hμ
    obtain ⟨q, hq, hrun⟩ := exists_run_eq_right (X := X) fun y => (htotal a y).choose
    refine ⟨{a}, Set.univ, q, hq.trans (le_max_right _ _), fun x hx y _ => ?_, ?_⟩
    · rw [Set.mem_singleton_iff.mp hx, hrun]
      exact (htotal a y).choose_spec
    · rw [PMF.toOuterMeasure_apply_singleton,
        (ν.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _), ENNReal.toReal_one]
      linarith
  by_cases hν : ∃ b, ((k : ℝ) ^ 2)⁻¹ ≤ (ν b).toReal
  · -- A heavy column: Alice announces a valid answer for the fixed input of Bob.
    obtain ⟨b, hb⟩ := hν
    obtain ⟨q, hq, hrun⟩ := exists_run_eq_left (Y := Y) fun x => (htotal x b).choose
    refine ⟨Set.univ, {b}, q, hq.trans (le_max_right _ _), fun x _ y hy => ?_, ?_⟩
    · rw [Set.mem_singleton_iff.mp hy, hrun]
      exact (htotal x b).choose_spec
    · rw [PMF.toOuterMeasure_apply_singleton,
        (μ.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _), ENNReal.toReal_one]
      linarith
  push Not at hμ hν
  obtain ⟨i, background, hlarge⟩ := exists_large_forcing_rectangle μ ν p hk
    (fun a => (hμ a).le) (fun b => (hν b).le)
  exact ⟨_, _, rectangleProtocol p i background, (depth_rectangleProtocol p i background).le.trans
    (le_max_left _ _), rectangleProtocol_solves hp i background, hlarge⟩

end Cslib.Communication.OneOut
