/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Card
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.Linarith

/-!
# Bimatrix games

A *bimatrix game* (`Cslib.GameTheory.BimatrixGame`) is a finite two-player game in strategic form,
given by two payoff matrices `A B : Matrix M N ℝ`: if player 1 plays the row `i` and player 2 the
column `j`, they receive `A i j` and `B i j`, which they maximize. A *mixed strategy* is a
probability vector (`Cslib.GameTheory.IsMixedStrategy`), and the expected payoffs of mixed
strategies `x` and `y` are `xᵀ A y` and `xᵀ B y`. A pair `(x, y)` is a (mixed) *Nash
equilibrium* (`BimatrixGame.IsNash`) if each strategy is a best response to the other. We follow
the conventions of [vonStengel2007], Section 3.2.

Mixed strategies are plain vectors `M → ℝ`, as in `Complexity.GameTheory.Strategic.Mixed`, so that
they can be fed to `Matrix.mulVec` and to the polyhedral API in
`Complexity.Foundations.LinearAlgebra.Matrix.Vertex`. They are exactly the weight vectors of the
points of `Convexity.StdSimplex ℝ M`, the representation of distributions used in
`Complexity.Probability.Minimax` and `Complexity.GameTheory.Strategic.Smooth`
(`Cslib.GameTheory.isMixedStrategy_iff_mem_range_weights`).

## Main definitions

* `Cslib.GameTheory.IsMixedStrategy`: a probability vector.
* `Cslib.GameTheory.BimatrixGame`: a bimatrix game, with expected payoffs `payoff₁` and `payoff₂`.
* `BimatrixGame.IsBestResponse₁`, `BimatrixGame.IsBestResponse₂`: mixed best responses.
* `BimatrixGame.IsPureBestResponse₁`, `BimatrixGame.IsPureBestResponse₂`: pure best responses.
* `BimatrixGame.IsNash`: a mixed Nash equilibrium.
* `BimatrixGame.IsNondegenerate`: no mixed strategy with support of size `k` has more than `k`
  pure best responses ([vonStengel2007], Definition 3.2).
* `BimatrixGame.addConst`: the game with a constant added to all payoffs.

## Main results

* `Cslib.GameTheory.IsMixedStrategy.forall_dotProduct_le_iff`: a probability vector maximizes a
  linear function over the simplex iff its support consists of maximizers.
* `BimatrixGame.isBestResponse₁_iff`, `BimatrixGame.isBestResponse₂_iff`: the *best response
  condition*, a mixed strategy is a best response iff every pure strategy in its support is a pure
  best response ([vonStengel2007], Proposition 3.1).
* `BimatrixGame.IsNash.ncard_support_eq`: in a Nash equilibrium of a nondegenerate game both
  strategies have supports of the same size ([vonStengel2007], Proposition 3.3).
* `BimatrixGame.isNash_addConst`, `BimatrixGame.isNondegenerate_addConst`: adding a constant to
  all payoffs changes neither the Nash equilibria nor nondegeneracy, and
  `BimatrixGame.exists_addConst_pos` makes all payoffs positive.

## References

* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007]
-/

public section

open Finset Matrix

namespace Cslib.GameTheory

section MixedStrategy

variable {ι : Type*} [Fintype ι] {x w : ι → ℝ} {c : ℝ}

/-- A *mixed strategy* over a finite set `ι` of pure strategies: a probability vector. -/
def IsMixedStrategy (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

theorem isMixedStrategy_iff : IsMixedStrategy x ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 :=
  Iff.rfl

theorem IsMixedStrategy.nonneg (hx : IsMixedStrategy x) (i : ι) : 0 ≤ x i := hx.1 i

theorem IsMixedStrategy.sum_eq_one (hx : IsMixedStrategy x) : ∑ i, x i = 1 := hx.2

/-- A mixed strategy plays some pure strategy with positive probability. -/
theorem IsMixedStrategy.exists_pos (hx : IsMixedStrategy x) : ∃ i, 0 < x i := by
  by_contra hne
  push Not at hne
  have : ∑ i, x i = 0 := sum_eq_zero fun i _ => le_antisymm (hne i) (hx.1 i)
  rw [hx.2] at this
  exact one_ne_zero this

theorem IsMixedStrategy.ne_zero (hx : IsMixedStrategy x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := hx.exists_pos
  exact lt_irrefl _ hi

/-- Averaging a positive vector under a mixed strategy gives a positive number. -/
theorem IsMixedStrategy.dotProduct_pos (hx : IsMixedStrategy x) (hw : ∀ i, 0 < w i) :
    0 < x ⬝ᵥ w := by
  obtain ⟨i, hi⟩ := hx.exists_pos
  exact (sum_pos_iff_of_nonneg fun j _ => mul_nonneg (hx.1 j) (hw j).le).2
    ⟨i, mem_univ _, mul_pos hi (hw i)⟩

/-- Normalizing a nonzero nonnegative vector gives a mixed strategy. -/
theorem isMixedStrategy_inv_sum_smul (hx : ∀ i, 0 ≤ x i) (hx₀ : x ≠ 0) :
    IsMixedStrategy ((∑ i, x i)⁻¹ • x) := by
  have hpos : 0 < ∑ i, x i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx₀
    exact (sum_pos_iff_of_nonneg fun j _ => hx j).2 ⟨i, mem_univ _, (hx i).lt_of_ne' hi⟩
  refine ⟨fun i => smul_nonneg (inv_nonneg.2 hpos.le) (hx i), ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
  exact inv_mul_cancel₀ hpos.ne'

/-- A mixed strategy is determined by the ray it spans. -/
theorem IsMixedStrategy.eq_of_smul_eq_smul {x' : ι → ℝ} {c' : ℝ} (hx : IsMixedStrategy x)
    (hx' : IsMixedStrategy x') (hc : c ≠ 0) (h : c • x = c' • x') : x = x' := by
  have hcc : c = c' := by
    have := congrArg (fun v : ι → ℝ => ∑ i, v i) h
    simpa only [Pi.smul_apply, smul_eq_mul, ← mul_sum, hx.2, hx'.2, mul_one] using this
  subst hcc
  exact smul_right_injective _ hc h

/-- Mixed strategies are the weight vectors of the points of `Convexity.StdSimplex ℝ ι`. -/
theorem isMixedStrategy_iff_mem_range_weights :
    IsMixedStrategy x ↔ x ∈ Set.range fun p : Convexity.StdSimplex ℝ ι => (p.weights : ι → ℝ) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  simp [IsMixedStrategy]

theorem isMixedStrategy_weights (p : Convexity.StdSimplex ℝ ι) :
    IsMixedStrategy (p.weights : ι → ℝ) :=
  isMixedStrategy_iff_mem_range_weights.2 ⟨p, rfl⟩

/-- A pure strategy, as a mixed strategy. -/
theorem isMixedStrategy_single [DecidableEq ι] (i : ι) : IsMixedStrategy (Pi.single i (1 : ℝ)) :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩

/-- Averaging a vector that equals `c` on the support of a mixed strategy gives `c`. -/
theorem IsMixedStrategy.dotProduct_eq_of_forall_pos (hx : IsMixedStrategy x)
    (h : ∀ i, 0 < x i → w i = c) : x ⬝ᵥ w = c := by
  calc x ⬝ᵥ w = ∑ i, x i * c := by
        refine sum_congr rfl fun i _ => ?_
        rcases (hx.1 i).lt_or_eq with hi | hi
        · rw [h i hi]
        · rw [← hi, zero_mul, zero_mul]
    _ = c := by rw [← sum_mul, hx.2, one_mul]

/-- Averaging a vector bounded by `c` under a mixed strategy gives at most `c`. -/
theorem IsMixedStrategy.dotProduct_le_of_forall_le (hx : IsMixedStrategy x) (h : ∀ i, w i ≤ c) :
    x ⬝ᵥ w ≤ c := by
  calc x ⬝ᵥ w = ∑ i, x i * w i := rfl
    _ ≤ ∑ i, x i * c := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hx.1 i)
    _ = c := by rw [← sum_mul, hx.2, one_mul]

/-- A mixed strategy maximizes the linear function `x ↦ x ⬝ᵥ w` over all mixed strategies iff every
pure strategy in its support maximizes `w`. -/
theorem IsMixedStrategy.forall_dotProduct_le_iff (hx : IsMixedStrategy x) :
    (∀ x', IsMixedStrategy x' → x' ⬝ᵥ w ≤ x ⬝ᵥ w) ↔ ∀ i, 0 < x i → ∀ i', w i' ≤ w i := by
  classical
  constructor
  · intro h i hi i'
    by_contra hlt
    push Not at hlt
    obtain ⟨i₀, -, hi₀⟩ := exists_max_image univ w ⟨i, mem_univ _⟩
    have h₁ := h _ (isMixedStrategy_single i₀)
    rw [single_dotProduct, one_mul] at h₁
    have h₂ : x ⬝ᵥ w < w i₀ := by
      calc x ⬝ᵥ w = ∑ j, x j * w j := rfl
        _ < ∑ j, x j * w i₀ := by
          refine sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hi₀ j (mem_univ _)) (hx.1 j))
            ⟨i, mem_univ _, mul_lt_mul_of_pos_left
              (hlt.trans_le (hi₀ i' (mem_univ _))) hi⟩
        _ = w i₀ := by rw [← sum_mul, hx.2, one_mul]
    linarith
  · intro h x' hx'
    obtain ⟨i₀, hi₀⟩ := hx.exists_pos
    rw [hx.dotProduct_eq_of_forall_pos fun i hi => le_antisymm (h i₀ hi₀ i) (h i hi i₀)]
    exact hx'.dotProduct_le_of_forall_le (h i₀ hi₀)

end MixedStrategy

/-- A *bimatrix game*: a finite two-player game in strategic form. Player 1 chooses a row `i : M`,
player 2 a column `j : N`, and they receive the payoffs `A i j` and `B i j`, which they
maximize. -/
structure BimatrixGame (M N : Type*) where
  /-- The payoff matrix of player 1, the row player. -/
  A : Matrix M N ℝ
  /-- The payoff matrix of player 2, the column player. -/
  B : Matrix M N ℝ

namespace BimatrixGame

variable {M N : Type*} [Fintype M] [Fintype N] (G : BimatrixGame M N)

/-- The expected payoff `xᵀ A y` of player 1. -/
def payoff₁ (x : M → ℝ) (y : N → ℝ) : ℝ := x ⬝ᵥ (G.A *ᵥ y)

/-- The expected payoff `xᵀ B y` of player 2. -/
def payoff₂ (x : M → ℝ) (y : N → ℝ) : ℝ := x ⬝ᵥ (G.B *ᵥ y)

/-- `x` is a *best response* of player 1 to `y`: a mixed strategy maximizing `payoff₁ · y` over all
mixed strategies. -/
def IsBestResponse₁ (x : M → ℝ) (y : N → ℝ) : Prop :=
  IsMixedStrategy x ∧ ∀ x', IsMixedStrategy x' → G.payoff₁ x' y ≤ G.payoff₁ x y

/-- `y` is a *best response* of player 2 to `x`: a mixed strategy maximizing `payoff₂ x ·` over all
mixed strategies. -/
def IsBestResponse₂ (y : N → ℝ) (x : M → ℝ) : Prop :=
  IsMixedStrategy y ∧ ∀ y', IsMixedStrategy y' → G.payoff₂ x y' ≤ G.payoff₂ x y

/-- `(x, y)` is a (mixed) *Nash equilibrium*: each strategy is a best response to the other. -/
def IsNash (x : M → ℝ) (y : N → ℝ) : Prop :=
  G.IsBestResponse₁ x y ∧ G.IsBestResponse₂ y x

/-- The row `i` is a *pure best response* of player 1 to `y`: it maximizes the expected payoff
`(A *ᵥ y) i`. -/
def IsPureBestResponse₁ (y : N → ℝ) (i : M) : Prop :=
  ∀ i', (G.A *ᵥ y) i' ≤ (G.A *ᵥ y) i

/-- The column `j` is a *pure best response* of player 2 to `x`: it maximizes the expected payoff
`(x ᵥ* B) j`. -/
def IsPureBestResponse₂ (x : M → ℝ) (j : N) : Prop :=
  ∀ j', (x ᵥ* G.B) j' ≤ (x ᵥ* G.B) j

/-- A bimatrix game is *nondegenerate* if no mixed strategy with support of size `k` has more than
`k` pure best responses ([vonStengel2007], Definition 3.2). -/
def IsNondegenerate : Prop :=
  (∀ x, IsMixedStrategy x → {j | G.IsPureBestResponse₂ x j}.ncard ≤ (Function.support x).ncard) ∧
    ∀ y, IsMixedStrategy y → {i | G.IsPureBestResponse₁ y i}.ncard ≤ (Function.support y).ncard

variable {G} {x : M → ℝ} {y : N → ℝ}

theorem payoff₁_eq_dotProduct (x : M → ℝ) (y : N → ℝ) : G.payoff₁ x y = x ⬝ᵥ (G.A *ᵥ y) := by
  rw [payoff₁]

theorem payoff₂_eq_dotProduct (x : M → ℝ) (y : N → ℝ) : G.payoff₂ x y = y ⬝ᵥ (x ᵥ* G.B) := by
  rw [payoff₂, dotProduct_mulVec, dotProduct_comm]

theorem isNash_iff : G.IsNash x y ↔ G.IsBestResponse₁ x y ∧ G.IsBestResponse₂ y x := Iff.rfl

omit [Fintype M] in
theorem isPureBestResponse₁_iff {i : M} :
    G.IsPureBestResponse₁ y i ↔ ∀ i', (G.A *ᵥ y) i' ≤ (G.A *ᵥ y) i := Iff.rfl

omit [Fintype N] in
theorem isPureBestResponse₂_iff {j : N} :
    G.IsPureBestResponse₂ x j ↔ ∀ j', (x ᵥ* G.B) j' ≤ (x ᵥ* G.B) j := Iff.rfl

theorem isNondegenerate_iff : G.IsNondegenerate ↔
    (∀ x, IsMixedStrategy x → {j | G.IsPureBestResponse₂ x j}.ncard ≤ (Function.support x).ncard) ∧
      ∀ y, IsMixedStrategy y → {i | G.IsPureBestResponse₁ y i}.ncard ≤ (Function.support y).ncard :=
  Iff.rfl

theorem IsBestResponse₁.isMixedStrategy (h : G.IsBestResponse₁ x y) : IsMixedStrategy x := h.1

theorem IsBestResponse₂.isMixedStrategy (h : G.IsBestResponse₂ y x) : IsMixedStrategy y := h.1

/-- **Best response condition** for player 1 ([vonStengel2007], Proposition 3.1): a mixed strategy
is a best response iff every row it plays with positive probability is a pure best response. -/
theorem isBestResponse₁_iff :
    G.IsBestResponse₁ x y ↔ IsMixedStrategy x ∧ ∀ i, 0 < x i → G.IsPureBestResponse₁ y i :=
  ⟨fun h => ⟨h.1, h.1.forall_dotProduct_le_iff.1 h.2⟩,
    fun h => ⟨h.1, h.1.forall_dotProduct_le_iff.2 h.2⟩⟩

/-- **Best response condition** for player 2 ([vonStengel2007], Proposition 3.1). -/
theorem isBestResponse₂_iff :
    G.IsBestResponse₂ y x ↔ IsMixedStrategy y ∧ ∀ j, 0 < y j → G.IsPureBestResponse₂ x j := by
  simp only [IsBestResponse₂, payoff₂_eq_dotProduct]
  exact ⟨fun h => ⟨h.1, h.1.forall_dotProduct_le_iff.1 h.2⟩,
    fun h => ⟨h.1, h.1.forall_dotProduct_le_iff.2 h.2⟩⟩

/-- Against `y`, a best response earns the payoff of each row in its support. -/
theorem IsBestResponse₁.payoff₁_eq_of_pos (h : G.IsBestResponse₁ x y) {i : M} (hi : 0 < x i) :
    G.payoff₁ x y = (G.A *ᵥ y) i :=
  h.1.dotProduct_eq_of_forall_pos fun i' hi' =>
    le_antisymm ((isBestResponse₁_iff.1 h).2 i hi i') ((isBestResponse₁_iff.1 h).2 i' hi' i)

/-- Against `y`, a best response earns at least the payoff of every row. -/
theorem IsBestResponse₁.le_payoff₁ (h : G.IsBestResponse₁ x y) (i : M) :
    (G.A *ᵥ y) i ≤ G.payoff₁ x y := by
  classical
  have := h.2 _ (isMixedStrategy_single i)
  rwa [payoff₁, single_dotProduct, one_mul] at this

/-- Against `x`, a best response earns the payoff of each column in its support. -/
theorem IsBestResponse₂.payoff₂_eq_of_pos (h : G.IsBestResponse₂ y x) {j : N} (hj : 0 < y j) :
    G.payoff₂ x y = (x ᵥ* G.B) j := by
  rw [payoff₂_eq_dotProduct]
  exact h.1.dotProduct_eq_of_forall_pos fun j' hj' =>
    le_antisymm ((isBestResponse₂_iff.1 h).2 j hj j') ((isBestResponse₂_iff.1 h).2 j' hj' j)

/-- Against `x`, a best response earns at least the payoff of every column. -/
theorem IsBestResponse₂.le_payoff₂ (h : G.IsBestResponse₂ y x) (j : N) :
    (x ᵥ* G.B) j ≤ G.payoff₂ x y := by
  classical
  have := h.2 _ (isMixedStrategy_single j)
  rwa [payoff₂_eq_dotProduct x (Pi.single j 1), single_dotProduct, one_mul] at this

/-- With positive payoffs, player 1 earns a positive expected payoff. -/
theorem payoff₁_pos (hA : ∀ i j, 0 < G.A i j) (hx : IsMixedStrategy x) (hy : IsMixedStrategy y) :
    0 < G.payoff₁ x y :=
  hx.dotProduct_pos fun i => by
    change 0 < G.A i ⬝ᵥ y
    rw [dotProduct_comm]
    exact hy.dotProduct_pos (hA i)

/-- With positive payoffs, player 2 earns a positive expected payoff. -/
theorem payoff₂_pos (hB : ∀ i j, 0 < G.B i j) (hx : IsMixedStrategy x) (hy : IsMixedStrategy y) :
    0 < G.payoff₂ x y := by
  rw [payoff₂_eq_dotProduct]
  exact hy.dotProduct_pos fun j => hx.dotProduct_pos fun i => hB i j

/-- In a Nash equilibrium of a nondegenerate bimatrix game, both strategies have supports of the
same size ([vonStengel2007], Proposition 3.3). -/
theorem IsNash.ncard_support_eq (hG : G.IsNondegenerate) (h : G.IsNash x y) :
    (Function.support x).ncard = (Function.support y).ncard := by
  have h₁ : Function.support x ⊆ {i | G.IsPureBestResponse₁ y i} := fun i hi =>
    (isBestResponse₁_iff.1 h.1).2 i (lt_of_le_of_ne (h.1.1.1 i) (Ne.symm hi))
  have h₂ : Function.support y ⊆ {j | G.IsPureBestResponse₂ x j} := fun j hj =>
    (isBestResponse₂_iff.1 h.2).2 j (lt_of_le_of_ne (h.2.1.1 j) (Ne.symm hj))
  have := (Set.ncard_le_ncard h₁ (Set.toFinite _)).trans (hG.2 y h.2.1)
  have := (Set.ncard_le_ncard h₂ (Set.toFinite _)).trans (hG.1 x h.1.1)
  omega

/-! ### Adding a constant to all payoffs -/

variable (G) in
/-- The game with the constant `c` added to every payoff of both players. -/
def addConst (c : ℝ) : BimatrixGame M N :=
  ⟨G.A + of fun _ _ => c, G.B + of fun _ _ => c⟩

omit [Fintype M] [Fintype N] in
@[simp]
theorem addConst_A_apply (c : ℝ) (i : M) (j : N) : (G.addConst c).A i j = G.A i j + c := by
  rw [addConst]
  rfl

omit [Fintype M] [Fintype N] in
@[simp]
theorem addConst_B_apply (c : ℝ) (i : M) (j : N) : (G.addConst c).B i j = G.B i j + c := by
  rw [addConst]
  rfl

omit [Fintype M] in
theorem addConst_A_mulVec (c : ℝ) (y : N → ℝ) :
    (G.addConst c).A *ᵥ y = G.A *ᵥ y + fun _ => c * ∑ j, y j := by
  rw [addConst, add_mulVec]
  ext i
  simp [mulVec, dotProduct, mul_sum]

omit [Fintype N] in
theorem vecMul_addConst_B (c : ℝ) (x : M → ℝ) :
    x ᵥ* (G.addConst c).B = x ᵥ* G.B + fun _ => c * ∑ i, x i := by
  rw [addConst, vecMul_add]
  ext j
  simp [vecMul, dotProduct, mul_sum, mul_comm]

omit [Fintype M] in
@[simp]
theorem isPureBestResponse₁_addConst {c : ℝ} {i : M} :
    (G.addConst c).IsPureBestResponse₁ y i ↔ G.IsPureBestResponse₁ y i := by
  simp [IsPureBestResponse₁, addConst_A_mulVec]

omit [Fintype N] in
@[simp]
theorem isPureBestResponse₂_addConst {c : ℝ} {j : N} :
    (G.addConst c).IsPureBestResponse₂ x j ↔ G.IsPureBestResponse₂ x j := by
  simp [IsPureBestResponse₂, vecMul_addConst_B]

/-- Adding a constant to all payoffs does not change the Nash equilibria. -/
@[simp]
theorem isNash_addConst {c : ℝ} : (G.addConst c).IsNash x y ↔ G.IsNash x y := by
  simp [IsNash, isBestResponse₁_iff, isBestResponse₂_iff]

/-- Adding a constant to all payoffs does not change nondegeneracy. -/
@[simp]
theorem isNondegenerate_addConst {c : ℝ} :
    (G.addConst c).IsNondegenerate ↔ G.IsNondegenerate := by
  simp [IsNondegenerate]

omit [Fintype M] [Fintype N] in
variable (G) in
/-- A large enough constant makes all payoffs positive. -/
theorem exists_addConst_pos [Finite M] [Finite N] :
    ∃ c, (∀ i j, 0 < (G.addConst c).A i j) ∧ ∀ i j, 0 < (G.addConst c).B i j := by
  obtain ⟨c, hc⟩ :=
    (Set.toFinite (Set.range fun p : M × N => max (-G.A p.1 p.2) (-G.B p.1 p.2))).bddAbove
  refine ⟨c + 1, fun i j => ?_, fun i j => ?_⟩
  · have : -G.A i j ≤ c := (le_max_left _ _).trans (hc ⟨(i, j), rfl⟩)
    rw [addConst_A_apply]
    linarith
  · have : -G.B i j ≤ c := (le_max_right _ _).trans (hc ⟨(i, j), rfl⟩)
    rw [addConst_B_apply]
    linarith

end BimatrixGame

end Cslib.GameTheory
