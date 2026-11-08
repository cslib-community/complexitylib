/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Query.FreeM.CostHom
import Complexity.Algorithms.Lean.Query.ShortestPaths.NegTriangleSubcubic
import Mathlib.Data.Fin.VecNotation

/-!
# Negative triangles and the (min,+) product

Kernel-checked instances of the negative triangle predicates (a graph with a negative triangle and
one without); runs of the schoolbook detector, of finding by halving, of the blocking reduction,
of the binary search and of the whole reduction from the (min,+) product to negative triangle
detection over `MinTropical (WithTop ℤ)` with the honest oracle, with query counts; and the general
theorems instantiated with the schoolbook detector, including the exponent bound with `δ = 0` and
real weights, which shows that their hypotheses are satisfiable.
-/

namespace ComplexityTests.NegativeTriangle

open MinTropical Cslib Cslib.Query Cslib.Algorithms.ShortestPaths

/-- Weights in `ℤ ∪ {∞}`, with `0 = ∞` (no edge) and `1 = 0`. -/
abbrev T := MinTropical (WithTop ℤ)

/-- The honest oracle: an addition query is a minimum, a multiplication query adds weights. -/
def oracle : {ι : Type} → ArithQuery T ι → ι
  | _, .add a b => a + b
  | _, .sub a _ => a
  | _, .mul a b => a * b

theorem oracle_add (a b : T) : oracle (.add a b) = a + b := rfl
theorem oracle_mul (a b : T) : oracle (.mul a b) = a * b := rfl

/-- The finite weight `x`. -/
def w (x : ℤ) : T := trop (x : WithTop ℤ)

instance (n : ℕ) : DecidableEq (Matrix (Fin n) (Fin n) T) :=
  inferInstanceAs (DecidableEq (Fin n → Fin n → T))

/-- `I`–`K` weights: `0–0` is `1`, `1–1` is `-3`, no edge `0–1`, and `1–0` is `2`. -/
def A₂ : Matrix (Fin 2) (Fin 2) T := Matrix.of ![![w 1, 0], ![w 2, w (-3)]]

/-- `K`–`J` weights. -/
def B₂ : Matrix (Fin 2) (Fin 2) T := Matrix.of ![![w 4, 0], ![w (-1), w 5]]

/-- The (min,+) product: `(A₂ * B₂) 1 0 = min (2 + 4, -3 - 1) = -4`. -/
def P₂ : Matrix (Fin 2) (Fin 2) T := Matrix.of ![![w 5, 0], ![w (-4), w 2]]

/-- With `C 1 0 = 3`, the triangle `(1, 0, 1)` has weight `-3 - 1 + 3 = -1 < 0`. -/
def Cyes : Matrix (Fin 2) (Fin 2) T := Matrix.of ![![w 0, w 0], ![w 3, w 0]]

/-- With `C = 5`, every triangle has weight at least `1`. -/
def Cno : Matrix (Fin 2) (Fin 2) T := Matrix.of ![![w 5, w 5], ![w 5, w 5]]

/-! ### The predicates -/

example : A₂ * B₂ = P₂ := by decide +kernel
example : IsNegTriangle A₂ B₂ Cyes 1 0 1 := by decide +kernel
example : ¬ IsNegTriangle A₂ B₂ Cyes 1 0 0 := by decide +kernel
example : OnNegTriangle A₂ B₂ Cyes 1 0 := by decide +kernel
example : ¬ OnNegTriangle A₂ B₂ Cyes 0 0 := by decide +kernel
example : HasNegTriangle A₂ B₂ Cyes := by decide +kernel
example : ¬ HasNegTriangle A₂ B₂ Cno := by decide +kernel
/-- A decidable test for `FiniteEntriesBounded`. -/
theorem finiteEntriesBounded_of {n : ℕ} {P : Matrix (Fin n) (Fin n) T} {W : ℕ}
    (h : ∀ i j, untrop (P i j) ≠ ⊤ → |(untrop (P i j)).untopD 0| ≤ W) :
    FiniteEntriesBounded P W := fun i j x hx => by
  have := h i j (by rw [hx]; exact WithTop.coe_ne_top)
  rwa [hx, WithTop.untopD_coe] at this

theorem bounded_P₂ : FiniteEntriesBounded P₂ 5 := finiteEntriesBounded_of (by decide +kernel)
example : ¬ FiniteEntriesBounded P₂ 4 := fun h => by
  have := h 0 0 5 rfl
  norm_num at this

/-! ### Runs and query counts -/

/-- The schoolbook detector: one schoolbook product, `8` multiplications and `4` additions. -/
example : (negTriViaMinPlus (schoolbookMatMul 2) A₂ B₂ Cyes).eval oracle = true := by
  decide +kernel
example : (negTriViaMinPlus (schoolbookMatMul 2) A₂ B₂ Cno).eval oracle = false := by
  decide +kernel
example : (negTriViaMinPlus (schoolbookMatMul 2) A₂ B₂ Cyes).countQueries oracle = 12 := by
  decide +kernel

/-- The schoolbook detector on parts of every size. -/
def det : (m : ℕ) → Matrix (Fin m) (Fin m) T → Matrix (Fin m) (Fin m) T →
    Matrix (Fin m) (Fin m) T → FreeM (ArithQuery T) Bool :=
  fun m => negTriViaMinPlus (schoolbookMatMul m)

/-- Finding by halving (`L = 1`) finds the unique negative triangle with `8 + 1` calls of the
detector on parts of size `1`, one multiplication each. -/
example : (findNegTri det 1 A₂ B₂ Cyes).eval oracle = some (1, 0, 1) := by decide +kernel
example : (findNegTri det 1 A₂ B₂ Cno).eval oracle = none := by decide +kernel
example : (findNegTri det 1 A₂ B₂ Cyes).countQueries oracle = 9 := by decide +kernel

/-- The blocking reduction with `2` blocks of size `1`: only the pair `(1, 0)` is on a negative
triangle. Each of the `8` block triples is drained with one unsuccessful call, and one call
succeeds. -/
example : (allPairsNegTri (t := 2) (κ := Fin 1) (fun A B C => findNegTri det 0 A B C)
    (A₂.submatrix finProdFinEquiv finProdFinEquiv) (B₂.submatrix finProdFinEquiv finProdFinEquiv)
    (Cyes.submatrix finProdFinEquiv finProdFinEquiv)).eval oracle =
      fun x y => decide (finProdFinEquiv x = 1 ∧ finProdFinEquiv y = 0) := by
  decide +kernel
example : (allPairsNegTri (t := 2) (κ := Fin 1) (fun A B C => findNegTri det 0 A B C)
    (A₂.submatrix finProdFinEquiv finProdFinEquiv) (B₂.submatrix finProdFinEquiv finProdFinEquiv)
    (Cyes.submatrix finProdFinEquiv finProdFinEquiv)).countQueries oracle = 9 := by
  decide +kernel

/-- The honest all-pairs subroutine, issuing no queries. -/
def apnt (A B C : Matrix (Fin 2) (Fin 2) T) : FreeM (ArithQuery T) (Fin 2 → Fin 2 → Bool) :=
  pure fun i j => decide (OnNegTriangle A B C i j)

/-- The binary search recovers `A₂ * B₂` with `⌈log₂ 12⌉ = 4` calls. -/
example : (minPlusViaAPNT 5 apnt A₂ B₂).eval oracle = P₂ := by decide +kernel

/-- The bound matters: `(A₂ * B₂) 0 0 = 5`, and the search on `[-4, 4] ∪ {⊤}` gets it wrong. -/
example : (minPlusViaAPNT 4 apnt A₂ B₂).eval oracle ≠ P₂ := by decide +kernel

/-- **The whole reduction**: the (min,+) product `A₂ * B₂` with the schoolbook detector, with
blocks of size `1`, `3` blocks and `⌈log₂ 12⌉ = 4` rounds of binary search. -/
example : (minPlusViaNegTri det 5 A₂ B₂).eval oracle = P₂ := by decide +kernel
/-- `4` rounds of `27` unsuccessful calls, and `6` successful ones, of the detector on parts of
size `1` (one multiplication each). The general bound `cost_minPlusViaNegTri_le` gives
`4 (3 ^ 3 + 3 ^ 2) = 144`. -/
example : (minPlusViaNegTri det 5 A₂ B₂).countQueries oracle = 114 := by decide +kernel

/-! ### The general theorems, instantiated -/

example (n M : ℕ) (A B : Matrix (Fin n) (Fin n) T) (hA : FiniteEntriesBounded A M)
    (hB : FiniteEntriesBounded B M) : (minPlusViaNegTri det (2 * M) A B).eval oracle = A * B :=
  eval_minPlusViaNegTri_of_bounded oracle
    (fun m A B C => eval_negTriViaMinPlus_schoolbook oracle oracle_add oracle_mul m A B C) hA hB

example : (minPlusViaNegTri det 5 A₂ B₂).eval oracle = A₂ * B₂ :=
  eval_minPlusViaNegTri oracle
    (fun m A B C => eval_negTriViaMinPlus_schoolbook oracle oracle_add oracle_mul m A B C)
    ((show A₂ * B₂ = P₂ by decide +kernel) ▸ bounded_P₂)

/-- The schoolbook detector, with unit weights in `ℝ`, costs at most `2 m ^ 3`. -/
theorem cost_det_le (m : ℕ) (A B C : Matrix (Fin m) (Fin m) T) :
    (det m A B C).cost oracle (fun q => (Nat.castAddMonoidHom ℝ) (ArithQuery.weight 1 1 q)) ≤
      2 * (m : ℝ) ^ ((3 : ℝ) - 0) := by
  rw [← FreeM.map_cost, det, cost_negTriViaMinPlus_schoolbook, sub_zero,
    show (3 : ℝ) = (3 : ℕ) from rfl, Real.rpow_natCast, Nat.coe_castAddMonoidHom]
  have : m ^ 2 * (m * 1 + (m - 1) * 1) ≤ 2 * m ^ 3 := by
    have : m - 1 ≤ m := Nat.sub_le m 1
    nlinarith
  exact_mod_cast this

/-- With `δ = 0` the exponent bound is cubic: `1088 ⌈log₂ (2 W + 2)⌉ n ^ 3`. -/
example (W n : ℕ) (hn : n ≠ 0) (A B : Matrix (Fin n) (Fin n) T) :
    (minPlusViaNegTri det W A B).cost oracle
        (fun q => (Nat.castAddMonoidHom ℝ) (ArithQuery.weight 1 1 q)) ≤
      544 * 2 * Nat.clog 2 (2 * W + 2) * (n : ℝ) ^ ((3 : ℝ) - 0 / 3) :=
  cost_minPlusViaNegTri_le_rpow oracle _ (by norm_num) (by norm_num) (fun m _ => cost_det_le m) W
    hn A B

end ComplexityTests.NegativeTriangle
