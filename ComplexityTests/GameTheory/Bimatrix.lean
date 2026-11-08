/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.GameTheory.Bimatrix.BestResponsePolytope

/-!
# Bimatrix games, vertices and the Lemke–Howson parity theorem

* The `3 × 2` game (3.3) of [vonStengel2007] has the pure equilibrium (top row, left column) and
  the two mixed equilibria `((4/5, 1/5, 0), (2/3, 1/3))` and `((0, 1/3, 2/3), (1/3, 2/3))`
  computed there; we check all three.
* The coordination game `A = B = 1` (the identity matrix) on any finite set of pure strategies is
  nondegenerate, so `odd_ncard_isNash` applies to it. With two strategies it has the three
  equilibria (both pure pairs and uniform mixing).
* The zero game is degenerate, and every pair of mixed strategies is an equilibrium: the
  nondegeneracy hypothesis of `odd_ncard_isNash` cannot be dropped (here `ncard = 0`).
* For the polyhedral API: the interval `0 ≤ t ≤ 1` has the vertex `0` but not the vertex `1/2`;
  repeating a row gives a degenerate system.
* In the positive coordination game `1 + 1`, the artificial pair `(0, 0)` is a node of degree `1`
  of the Lemke–Howson graph, the starting point of the algorithm.
-/

namespace ComplexityTests.GameTheory.Bimatrix

open Cslib.GameTheory Cslib.GameTheory.BimatrixGame Matrix

/-! ### Von Stengel's example (3.3) -/

/-- The `3 × 2` game (3.3) of [vonStengel2007]. -/
noncomputable def stengel : BimatrixGame (Fin 3) (Fin 2) :=
  ⟨!![3, 3; 2, 5; 0, 6], !![3, 2; 2, 6; 3, 1]⟩

private theorem isMixedStrategy_fin2 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 1) :
    IsMixedStrategy ![a, b] :=
  isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> simpa, by simpa [Fin.sum_univ_two] using h⟩

private theorem isMixedStrategy_fin3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : IsMixedStrategy ![a, b, c] :=
  isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> simpa,
    by simpa [Fin.sum_univ_three] using h⟩

/-- The pure equilibrium of (3.3): the top row and the left column. -/
theorem stengel_isNash_pure : stengel.IsNash ![1, 0, 0] ![1, 0] := by
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin3 (by norm_num) le_rfl le_rfl
    (by norm_num), fun i hi i' => ?_⟩, isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2 (by norm_num)
    le_rfl (by norm_num), fun j hj j' => ?_⟩⟩
  · revert hi
    fin_cases i <;> fin_cases i' <;> norm_num [stengel, mulVec, dotProduct, Fin.sum_univ_two]
  · revert hj
    fin_cases j <;> fin_cases j' <;> norm_num [stengel, vecMul, dotProduct, Fin.sum_univ_three]

/-- The first mixed equilibrium of (3.3). -/
theorem stengel_isNash_mixed₁ : stengel.IsNash ![4 / 5, 1 / 5, 0] ![2 / 3, 1 / 3] := by
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin3 (by norm_num) (by norm_num)
    le_rfl (by norm_num), fun i hi i' => ?_⟩, isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2
    (by norm_num) (by norm_num) (by norm_num), fun j hj j' => ?_⟩⟩
  · revert hi
    fin_cases i <;> fin_cases i' <;> norm_num [stengel, mulVec, dotProduct, Fin.sum_univ_two]
  · revert hj
    fin_cases j <;> fin_cases j' <;> norm_num [stengel, vecMul, dotProduct, Fin.sum_univ_three]

/-- The second mixed equilibrium of (3.3). -/
theorem stengel_isNash_mixed₂ : stengel.IsNash ![0, 1 / 3, 2 / 3] ![1 / 3, 2 / 3] := by
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin3 le_rfl (by norm_num)
    (by norm_num) (by norm_num), fun i hi i' => ?_⟩, isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2
    (by norm_num) (by norm_num) (by norm_num), fun j hj j' => ?_⟩⟩
  · revert hi
    fin_cases i <;> fin_cases i' <;> norm_num [stengel, mulVec, dotProduct, Fin.sum_univ_two]
  · revert hj
    fin_cases j <;> fin_cases j' <;> norm_num [stengel, vecMul, dotProduct, Fin.sum_univ_three]

/-- Against `y = (2/3, 1/3)` the bottom row is not a best response: `A y = (3, 3, 2)`
([vonStengel2007], Section 3.2), so `y` has only two pure best responses. -/
theorem stengel_not_isPureBestResponse₁ : ¬ stengel.IsPureBestResponse₁ ![2 / 3, 1 / 3] 2 := by
  rw [isPureBestResponse₁_iff]
  intro h
  have := h 0
  norm_num [stengel, mulVec, dotProduct, Fin.sum_univ_two] at this

/-! ### The coordination game -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordination game: both players receive `1` if they choose the same strategy. -/
def coord (ι : Type*) [DecidableEq ι] : BimatrixGame ι ι := ⟨1, 1⟩

omit [DecidableEq ι] in
/-- In the coordination game, a pure best response to a mixed strategy is played by it. -/
private theorem pos_of_forall_le {x : ι → ℝ} (hx : IsMixedStrategy x) {i : ι}
    (h : ∀ i', x i' ≤ x i) : 0 < x i := by
  obtain ⟨i', hi'⟩ := hx.exists_pos
  exact hi'.trans_le (h i')

omit [DecidableEq ι] in
private theorem ncard_le_of_forall_le {x : ι → ℝ} (hx : IsMixedStrategy x) :
    {i | ∀ i', x i' ≤ x i}.ncard ≤ (Function.support x).ncard :=
  Set.ncard_le_ncard (fun _ hi => (pos_of_forall_le hx hi).ne') (Set.toFinite _)

/-- The coordination game is nondegenerate: the pure best responses to a mixed strategy are among
the strategies it plays. -/
theorem coord_isNondegenerate : (coord ι).IsNondegenerate := by
  refine isNondegenerate_iff.2 ⟨fun x hx => ?_, fun y hy => ?_⟩
  · simpa only [isPureBestResponse₂_iff, coord, vecMul_one] using ncard_le_of_forall_le hx
  · simpa only [isPureBestResponse₁_iff, coord, one_mulVec] using ncard_le_of_forall_le hy

/-- The coordination game has an odd number of Nash equilibria. (For `n` strategies there are
`2ⁿ - 1`, uniform mixing over any nonempty common support; this count is not proved here.) -/
theorem coord_odd_ncard_isNash [Nonempty ι] :
    Odd {p : (ι → ℝ) × (ι → ℝ) | (coord ι).IsNash p.1 p.2}.ncard :=
  odd_ncard_isNash coord_isNondegenerate

/-- Uniform mixing is an equilibrium of the two-strategy coordination game. -/
theorem coord_isNash_uniform : (coord (Fin 2)).IsNash ![1 / 2, 1 / 2] ![1 / 2, 1 / 2] := by
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin2 (by norm_num) (by norm_num)
    (by norm_num), fun i _ i' => ?_⟩, isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2 (by norm_num)
    (by norm_num) (by norm_num), fun j _ j' => ?_⟩⟩
  · fin_cases i <;> fin_cases i' <;> simp [coord]
  · fin_cases j <;> fin_cases j' <;> simp [coord]

/-- Both pure coordination pairs are equilibria of the two-strategy coordination game. -/
theorem coord_isNash_pure (k : Fin 2) :
    (coord (Fin 2)).IsNash (Pi.single k 1) (Pi.single k 1) := by
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_single k, fun i hi i' => ?_⟩,
    isBestResponse₂_iff.2 ⟨isMixedStrategy_single k, fun j hj j' => ?_⟩⟩
  · fin_cases k <;> fin_cases i <;> fin_cases i' <;> simp [coord] at hi ⊢
  · fin_cases k <;> fin_cases j <;> fin_cases j' <;> simp [coord] at hj ⊢

/-! ### A degenerate game -/

/-- The zero game on two strategies each. -/
def zeroGame : BimatrixGame (Fin 2) (Fin 2) := ⟨0, 0⟩

/-- In the zero game every pair of mixed strategies is a Nash equilibrium. -/
theorem zeroGame_isNash {x y : Fin 2 → ℝ} (hx : IsMixedStrategy x) (hy : IsMixedStrategy y) :
    zeroGame.IsNash x y :=
  isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨hx, fun _ _ _ => by simp [zeroGame]⟩,
    isBestResponse₂_iff.2 ⟨hy, fun _ _ _ => by simp [zeroGame]⟩⟩

/-- The zero game is degenerate: a pure strategy has two pure best responses. -/
theorem zeroGame_not_isNondegenerate : ¬ zeroGame.IsNondegenerate := by
  intro h
  have := (isNondegenerate_iff.1 h).1 _ (isMixedStrategy_single (0 : Fin 2))
  have hall : {j | zeroGame.IsPureBestResponse₂ (Pi.single (0 : Fin 2) (1 : ℝ)) j} = Set.univ :=
    Set.eq_univ_of_forall fun j => isPureBestResponse₂_iff.2 fun _ => by simp [zeroGame]
  have hsupp : Function.support (Pi.single (0 : Fin 2) (1 : ℝ)) = {0} :=
    Pi.support_single_of_ne one_ne_zero
  rw [hall, hsupp, Set.ncard_univ, Set.ncard_singleton, Nat.card_eq_fintype_card,
    Fintype.card_fin] at this
  omega

/-- The zero game has infinitely many Nash equilibria, so the conclusion of `odd_ncard_isNash`
fails for it: `ncard` of an infinite set is `0`, which is even. -/
theorem zeroGame_infinite_isNash :
    {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | zeroGame.IsNash p.1 p.2}.Infinite := by
  have := Set.Icc.infinite (zero_lt_one' ℝ)
  refine Set.infinite_of_injective_forall_mem (α := Set.Icc (0 : ℝ) 1)
    (f := fun t => (![(t : ℝ), 1 - t], ![1, 0])) (fun s t h => ?_) (fun t => ?_)
  · have := congrFun (congrArg Prod.fst h) 0
    exact Subtype.ext (by simpa using this)
  · exact zeroGame_isNash (isMixedStrategy_fin2 t.2.1 (by linarith [t.2.2]) (by ring))
      (isMixedStrategy_fin2 (by norm_num) le_rfl (by norm_num))

theorem zeroGame_not_odd_ncard_isNash :
    ¬ Odd {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | zeroGame.IsNash p.1 p.2}.ncard := by
  rw [zeroGame_infinite_isNash.ncard]
  decide

/-! ### Vertices of a polyhedron -/

/-- The interval `0 ≤ t ≤ 1` as the system `-t ≤ 0`, `t ≤ 1`. -/
def intervalA : Matrix (Fin 2) (Fin 1) ℝ := !![-1; 1]

def intervalB : Fin 2 → ℝ := ![0, 1]

theorem isVertex_interval_zero : IsVertex intervalA intervalB 0 := by
  refine isVertex_iff.2 ⟨fun k => by fin_cases k <;> simp [intervalA, intervalB], fun v hv => ?_⟩
  have := hv 0 (by simp [intervalA, intervalB])
  funext i
  fin_cases i
  simpa [intervalA, mulVec, dotProduct] using this

theorem not_isVertex_interval_half : ¬ IsVertex intervalA intervalB (fun _ => 1 / 2) := by
  intro h
  have := (isVertex_iff.1 h).2 (fun _ => 1) fun k hk => by
    fin_cases k <;> norm_num [intervalA, intervalB, mulVec, dotProduct] at hk
  exact one_ne_zero (congrFun this 0)

/-- Repeating the row `t ≤ 1` makes the system degenerate: `t = 1` has two tight rows. -/
theorem not_isNondegenerateSystem_repeat :
    ¬ IsNondegenerateSystem (!![-1; 1; 1] : Matrix (Fin 3) (Fin 1) ℝ) ![0, 1, 1] := by
  intro h
  have := isNondegenerateSystem_iff.1 h (fun _ => 1) fun k => by
    fin_cases k <;> norm_num [mulVec, dotProduct]
  have hT :
      tightRows (!![-1; 1; 1] : Matrix (Fin 3) (Fin 1) ℝ) ![0, 1, 1] (fun _ => 1) = {1, 2} := by
    ext k
    fin_cases k <;> norm_num [mulVec, dotProduct]
  rw [hT] at this
  simp at this

/-! ### The start of the Lemke–Howson path -/

/-- The coordination game with all payoffs raised by `1`, so that they are positive. -/
def coordPos : BimatrixGame (Fin 2) (Fin 2) := (coord (Fin 2)).addConst 1

theorem coordPos_A_pos (i j : Fin 2) : 0 < coordPos.A i j := by
  rw [coordPos, addConst_A_apply]
  by_cases h : i = j <;> simp [coord, h]

theorem coordPos_B_pos (i j : Fin 2) : 0 < coordPos.B i j := by
  rw [coordPos, addConst_B_apply]
  by_cases h : i = j <;> simp [coord, h]

theorem coordPos_isNondegenerate : coordPos.IsNondegenerate :=
  isNondegenerate_addConst.2 coord_isNondegenerate

/-- The artificial equilibrium `(0, 0)`, as a node of the Lemke–Howson graph for the missing
label `inl 0`. -/
noncomputable def artificialNode :
    LemkeHowson.Node coordPos.matP (rhsP (Fin 2) (Fin 2)) coordPos.matQ (rhsQ (Fin 2) (Fin 2))
      (.inl 0) :=
  ⟨0, 0, isVertex_matP_zero, isVertex_matQ_zero, fun j _ =>
    (LemkeHowson.completelyLabeled_iff.1 (completelyLabeled_iff_forall.2
      ⟨fun _ => .inl rfl, fun _ => .inr rfl⟩)) j⟩

/-- The artificial equilibrium has exactly one neighbour: the Lemke–Howson path starts there. -/
theorem ncard_neighborSet_artificialNode :
    ((LemkeHowson.graph _ _ _ _ _).neighborSet artificialNode).ncard = 1 :=
  LemkeHowson.ncard_neighborSet_of_completelyLabeled
    coordPos_isNondegenerate.isNondegenerateSystem_matP
    (fun _ => eq_zero_of_matP_mulVec_nonpos coordPos_B_pos)
    coordPos_isNondegenerate.isNondegenerateSystem_matQ
    (fun _ => eq_zero_of_matQ_mulVec_nonpos coordPos_A_pos) Fintype.card_sum artificialNode
    (completelyLabeled_iff_forall.2 ⟨fun _ => .inl rfl, fun _ => .inr rfl⟩)

end ComplexityTests.GameTheory.Bimatrix
