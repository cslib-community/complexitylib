/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.RationalVertex
public import CslibFrontier.GameTheory.Bimatrix.ShapleyOrientation
public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses
public import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
public import CslibFrontier.Computability.Circuit.Rational.Runtime.Point
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.PolyTime.Int.DotProduct
public import CslibFrontier.Computability.PolyTime.Int.ExactDiv
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
import CslibFrontier.Computability.PolyTime.Int.Table
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Data.List.GetD

/-!
# Two-player Nash equilibrium is in PPAD

Finding a mixed Nash equilibrium of a two-player bimatrix game with rational payoffs belongs to
`PPAD` [Papadimitriou1994PPAD], [vonStengel2007], Chapter 3.

Payoff matrices are encoded by the structure `BimatrixCode` (fields `matA`, `matB`) under
`encBimatrix` using `Turing.MultiTapeTM.encRat`, and rational mixed strategy pairs by
`StrategyPair` under `encWitness`.
For well-formed nonempty `m × n` matrices, `BimatrixNash c w` holds when `w` is a polynomially
bounded canonical rational strategy pair forming an exact Nash equilibrium of `c.toGame`.
Non-well-formed inputs admit only the empty witness `[]`.

The reduction to `EndOfLine` normalizes `(A, B)` to positive integers in `[1, H]`, perturbs the
right-hand sides of the best-response polytopes `(P, Q)` by powers of `K_B = 2 ^ bitBound m n H`,
and walks completely-labelled / `k₀ = 0`-almost-completely-labelled basis pairs `(T₁, T₂)`
represented by `2 * (m + n)` bits (with the artificial origin `(T₁⁰, T₂⁰)` mapped to `0^(2(m+n))`).
Incident half-edges are oriented by Shapley's determinant index (`ShapleyOrientation`), pivoting
without division via `detRows` and `cramerRows`. Every unbalanced non-origin vertex yields an
unperturbed exact rational Nash equilibrium by Cramer rounding (`RationalVertex`), giving a
polynomial-time search reduction to `endOfLineRel` (`BimatrixNash_mem_PPAD`).

## Main definitions

* `Cslib.GameTheory.StrategyPair`, `Cslib.GameTheory.encWitness`: encoded rational strategy pair.
* `Cslib.GameTheory.BimatrixCode`, `Cslib.GameTheory.encBimatrix`: encoded bimatrix games.
* `Cslib.GameTheory.BimatrixCode.WellFormed`, `Cslib.GameTheory.BimatrixCode.toGame`:
  rectangularity predicate and induced `BimatrixGame`.
* `Cslib.GameTheory.BimatrixCode.IsRationalNash`, `Cslib.GameTheory.BimatrixCode.BimatrixNash`:
  the rational Nash search problem.
* `Cslib.GameTheory.BimatrixCode.vertexLen`, `Cslib.GameTheory.BimatrixCode.pred`,
  `Cslib.GameTheory.BimatrixCode.succ`, `Cslib.GameTheory.BimatrixCode.extractNash`:
  polynomial-time directed graph maps and witness extraction.

## Main results

* `Cslib.GameTheory.BimatrixCode.BimatrixNash.isNash`: witnesses decode to Nash equilibria.
* `Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_FNP`: `BimatrixNash ∈ FNP encBimatrix`.
* `Cslib.GameTheory.BimatrixCode.BimatrixNash_searchReducible_endOfLineRel`,
  `Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_PPAD`: two-player Nash is in `PPAD`.
* `Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_TFNP`,
  `Cslib.GameTheory.BimatrixCode.BimatrixNash_isTotalSearch`,
  `Cslib.GameTheory.BimatrixCode.BimatrixNash_searchReducible_EndOfLine`: totality and
  completeness corollaries.

## References

* [C. E. Lemke and J. T. Howson, Jr., *Equilibrium points of bimatrix games*][LemkeHowson1964]
* [L. S. Shapley, *A note on the Lemke–Howson algorithm*][Shapley1974]
* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007], Chapter 3
-/

public section

namespace Cslib.GameTheory

open Cslib Cslib.BitString Cslib.Circuits.Rational Cslib.Complexity Cslib.GameTheory.BimatrixGame
  Mathlib.Tactic.Matrix Matrix
open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Section 1: Encodings, games, and the rational Nash search problem -/

private abbrev encWitnessPairs : (List (ℤ × ℕ) × List (ℤ × ℕ)) ↪ List Bool :=
  encPair (encList encRatData) (encList encRatData)

/-- A pair of rational mixed strategy lists `(x, y)` for players 1 and 2. -/
@[ext]
structure StrategyPair where
  /-- Player 1's rational mixed strategy list. -/
  x : List ℚ
  /-- Player 2's rational mixed strategy list. -/
  y : List ℚ
deriving DecidableEq, Repr

/-- Canonical encoding of a rational strategy pair `(x, y)` via `Turing.MultiTapeTM.encRat`. -/
enc_structure encWitness : StrategyPair where
  x : (encList encRat),
  y : (encList encRat)

/-- An explicitly presented two-player game given by two lists of rational payoff rows. -/
@[ext]
structure BimatrixCode where
  /-- Player 1's rational payoff matrix as a list of rows. -/
  matA : List (List ℚ)
  /-- Player 2's rational payoff matrix as a list of rows. -/
  matB : List (List ℚ)
deriving DecidableEq, Repr

/-- Binary encoding of rational bimatrix games as `(matA, matB)` via `encRat`. -/
enc_structure encBimatrix : BimatrixCode where
  matA : (encList (encList encRat)),
  matB : (encList (encList encRat))

namespace BimatrixCode

/-- Number of pure strategies of player 1. -/
@[expose] def rows (c : BimatrixCode) : ℕ := c.matA.length

/-- Number of pure strategies of player 2. -/
@[expose] def cols (c : BimatrixCode) : ℕ := (c.matA.headD []).length

/-- Decidable rectangularity and nonemptiness check for `BimatrixCode`. -/
@[expose] def wellFormedB (c : BimatrixCode) : Bool :=
  decide (0 < c.rows) && decide (0 < c.cols) && decide (c.matB.length = c.rows) &&
    c.matA.all (fun r => decide (r.length = c.cols)) &&
    c.matB.all (fun r => decide (r.length = c.cols))

/-- Predicate asserting `c` encodes nonempty rectangular `rows × cols` payoff matrices. -/
@[expose] def WellFormed (c : BimatrixCode) : Prop :=
  0 < c.rows ∧ 0 < c.cols ∧ c.matB.length = c.rows ∧
    (∀ r ∈ c.matA, r.length = c.cols) ∧ (∀ r ∈ c.matB, r.length = c.cols)

theorem wellFormed_iff_wellFormedB (c : BimatrixCode) : c.WellFormed ↔ c.wellFormedB = true := by
  simp only [WellFormed, wellFormedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  tauto

/-- Player 1's rational payoff matrix extracted from `c`. -/
@[expose] def toMatA (c : BimatrixCode) : Matrix (Fin c.rows) (Fin c.cols) ℚ :=
  fun i j => (c.matA.getD i.1 []).getD j.1 0

/-- Player 2's rational payoff matrix extracted from `c`. -/
@[expose] def toMatB (c : BimatrixCode) : Matrix (Fin c.rows) (Fin c.cols) ℚ :=
  fun i j => (c.matB.getD i.1 []).getD j.1 0

/-- The `BimatrixGame` induced by a `BimatrixCode`. -/
@[expose] noncomputable def toGame (c : BimatrixCode) : BimatrixGame (Fin c.rows) (Fin c.cols) :=
  BimatrixGame.mk ((toMatA c).map Rat.cast) ((toMatB c).map Rat.cast)

/-- Pure rational Nash condition on strategy lists `x` (length `c.rows`) and `y`
(length `c.cols`). -/
@[expose] def IsRationalNash (c : BimatrixCode) (x y : List ℚ) : Prop :=
  x.length = c.rows ∧ y.length = c.cols ∧
    (∀ q ∈ x, 0 ≤ q) ∧ x.sum = 1 ∧
    (∀ q ∈ y, 0 ≤ q) ∧ y.sum = 1 ∧
    (∀ i : Fin c.rows,
      (∑ j : Fin c.cols, c.toMatA i j * y.getD j.1 0) ≤
        ∑ a : Fin c.rows, ∑ j : Fin c.cols, x.getD a.1 0 * c.toMatA a j * y.getD j.1 0) ∧
    (∀ j : Fin c.cols,
      (∑ i : Fin c.rows, x.getD i.1 0 * c.toMatB i j) ≤
        ∑ i : Fin c.rows, ∑ b : Fin c.cols, x.getD i.1 0 * c.toMatB i b * y.getD b.1 0)

private lemma fin_sum_getD_eq_list_sum {α : Type*} [AddCommMonoid α] (l : List α)
    (d : α) {n : ℕ} (hn : l.length = n) :
    (∑ i : Fin n, l.getD i.1 d) = l.sum := by
  subst hn
  induction l with
  | nil => simp
  | cons a l ih =>
    dsimp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.sum_cons]
    exact congrArg (a + ·) ih

theorem IsRationalNash.toGame_isNash {c : BimatrixCode} {x y : List ℚ}
    (hn : c.IsRationalNash x y) :
    c.toGame.IsNash (fun i : Fin c.rows => (x.getD i.1 0 : ℝ))
      (fun j : Fin c.cols => (y.getD j.1 0 : ℝ)) := by
  obtain ⟨hxlen, hylen, hxnn, hxsum, hynn, hysum, hbr1, hbr2⟩ := hn
  let xR : Fin c.rows → ℝ := fun i => (x.getD i.1 0 : ℝ)
  let yR : Fin c.cols → ℝ := fun j => (y.getD j.1 0 : ℝ)
  have hx_sum : ∑ i : Fin c.rows, xR i = 1 := by
    have hq : (∑ i : Fin c.rows, x.getD i.1 0) = 1 := by
      rw [fin_sum_getD_eq_list_sum x 0 hxlen, hxsum]
    simpa only [xR, ← Rat.cast_sum, Rat.cast_one] using congrArg (Rat.cast : ℚ → ℝ) hq
  have hy_sum : ∑ j : Fin c.cols, yR j = 1 := by
    have hq : (∑ j : Fin c.cols, y.getD j.1 0) = 1 := by
      rw [fin_sum_getD_eq_list_sum y 0 hylen, hysum]
    simpa only [yR, ← Rat.cast_sum, Rat.cast_one] using congrArg (Rat.cast : ℚ → ℝ) hq
  have hx_nn : ∀ i : Fin c.rows, 0 ≤ xR i := fun i =>
    Rat.cast_nonneg.2 (hxnn _ (by
      rw [List.getD_eq_getElem x 0 (by omega)]
      exact List.getElem_mem (by omega)))
  have hy_nn : ∀ j : Fin c.cols, 0 ≤ yR j := fun j =>
    Rat.cast_nonneg.2 (hynn _ (by
      rw [List.getD_eq_getElem y 0 (by omega)]
      exact List.getElem_mem (by omega)))
  have hmx : IsMixedStrategy xR := by
    rw [isMixedStrategy_iff]
    exact ⟨hx_nn, hx_sum⟩
  have hmy : IsMixedStrategy yR := by
    rw [isMixedStrategy_iff]
    exact ⟨hy_nn, hy_sum⟩
  rw [BimatrixGame.isNash_iff, BimatrixGame.isBestResponse₁_iff, BimatrixGame.isBestResponse₂_iff]
  refine ⟨⟨hmx, fun i hi => ?_⟩, ⟨hmy, fun j hj => ?_⟩⟩
  · rw [BimatrixGame.isPureBestResponse₁_iff]
    have hpt : ∀ a : Fin c.rows,
        ((c.toGame.A *ᵥ yR) a : ℝ) ≤ ∑ a' : Fin c.rows, xR a' * (c.toGame.A *ᵥ yR) a' := by
      intro a
      have ha := (Rat.cast_le (K := ℝ)).2 (hbr1 a)
      simpa only [xR, yR, toGame, Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum,
        Rat.cast_mul, Finset.mul_sum, mul_assoc] using ha
    have hi_eq : (c.toGame.A *ᵥ yR) i = ∑ a' : Fin c.rows, xR a' * (c.toGame.A *ᵥ yR) a' := by
      by_contra hne
      have hlt : (c.toGame.A *ᵥ yR) i < ∑ a' : Fin c.rows, xR a' * (c.toGame.A *ᵥ yR) a' :=
        lt_of_le_of_ne (hpt i) hne
      have hsum_lt : (∑ a : Fin c.rows, xR a * (c.toGame.A *ᵥ yR) a) <
          ∑ a : Fin c.rows, xR a * (∑ a' : Fin c.rows, xR a' * (c.toGame.A *ᵥ yR) a') :=
        Finset.sum_lt_sum
          (fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hx_nn a))
          ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hlt hi⟩
      rw [← Finset.sum_mul, hx_sum, one_mul] at hsum_lt
      exact (lt_irrefl _ hsum_lt).elim
    intro i'
    exact (hpt i').trans_eq hi_eq.symm
  · rw [BimatrixGame.isPureBestResponse₂_iff]
    have hpt : ∀ b : Fin c.cols,
        ((xR ᵥ* c.toGame.B) b : ℝ) ≤ ∑ b' : Fin c.cols, (xR ᵥ* c.toGame.B) b' * yR b' := by
      intro b
      have hb := (Rat.cast_le (K := ℝ)).2 (hbr2 b)
      rw [Finset.sum_comm] at hb
      simpa only [xR, yR, toGame, Matrix.vecMul, dotProduct, Matrix.map_apply, Rat.cast_sum,
        Rat.cast_mul, Finset.sum_mul, mul_assoc] using hb
    have hj_eq : (xR ᵥ* c.toGame.B) j = ∑ b' : Fin c.cols, (xR ᵥ* c.toGame.B) b' * yR b' := by
      by_contra hne
      have hlt : (xR ᵥ* c.toGame.B) j < ∑ b' : Fin c.cols, (xR ᵥ* c.toGame.B) b' * yR b' :=
        lt_of_le_of_ne (hpt j) hne
      have hsum_lt : (∑ b : Fin c.cols, (xR ᵥ* c.toGame.B) b * yR b) <
          ∑ b : Fin c.cols, (∑ b' : Fin c.cols, (xR ᵥ* c.toGame.B) b' * yR b') * yR b :=
        Finset.sum_lt_sum
          (fun b _ => mul_le_mul_of_nonneg_right (hpt b) (hy_nn b))
          ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_right hlt hj⟩
      rw [← Finset.mul_sum, hy_sum, mul_one] at hsum_lt
      exact (lt_irrefl _ hsum_lt).elim
    intro j'
    exact (hpt j').trans_eq hj_eq.symm

/-- Polynomial witness length bound `120 * L^3 + 400 * L + 100` in `L = (encBimatrix c).length`. -/
@[expose] noncomputable def witnessPoly : Polynomial ℕ :=
  Polynomial.C 120 * Polynomial.X ^ 3 + Polynomial.C 400 * Polynomial.X + Polynomial.C 100

theorem witnessPoly_eval (L : ℕ) :
    witnessPoly.eval L = 120 * L ^ 3 + 400 * L + 100 := by
  simp only [witnessPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

/-- The rational bimatrix Nash search problem: given `c`, find a polynomially bounded canonical
rational strategy pair `s` forming an exact Nash equilibrium of `c.toGame` (or `[]` on malformed
`c`). -/
@[expose] def BimatrixNash (c : BimatrixCode) (w : List Bool) : Prop :=
  if c.wellFormedB then
    w.length ≤ 120 * (encBimatrix c).length ^ 3 + 400 * (encBimatrix c).length + 100 ∧
      ∃ s : StrategyPair, w = encWitness s ∧ c.IsRationalNash s.x s.y
  else w = []

/-- Every solution witness of a well-formed game decodes to a Nash equilibrium of `c.toGame`. -/
theorem BimatrixNash.isNash {c : BimatrixCode} {w : List Bool}
    (hc : c.WellFormed) (hw : BimatrixNash c w) :
    ∃ s : StrategyPair, w = encWitness s ∧
      c.toGame.IsNash (fun i : Fin c.rows => (s.x.getD i.1 0 : ℝ))
        (fun j : Fin c.cols => (s.y.getD j.1 0 : ℝ)) := by
  have hwb : c.wellFormedB = true := (wellFormed_iff_wellFormedB c).1 hc
  simp only [BimatrixNash, hwb, ite_true] at hw
  obtain ⟨-, s, rfl, hrat⟩ := hw
  exact ⟨s, rfl, hrat.toGame_isNash⟩

/-! ### Section 2: Executable positive integer normalization -/

/-- Product of all rational denominators appearing in `c`. -/
private def clearScale (c : BimatrixCode) : ℤ :=
  (c.matA.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod *
    (c.matB.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod

/-- Scale a single rational `q` by `D` via exact truncated division `q.num * (D.tdiv q.den)`. -/
private def scaledEntry (D : ℤ) (q : ℚ) : ℤ :=
  q.num * (D.tdiv (q.den : ℤ))

/-- Clear denominators of a matrix of rationals using scale factor `D`. -/
private def clearMat (D : ℤ) (M : List (List ℚ)) : List (List ℤ) :=
  M.map fun row => row.map (scaledEntry D)

/-- Positive integer shift `1 + ∑ |scaled entries|` ensuring all payoffs are strictly positive. -/
private def shiftVal (c : BimatrixCode) : ℤ :=
  let D := clearScale c
  1 + (c.matA.map fun row => (row.map fun q => |(scaledEntry D q)|).sum).sum +
    (c.matB.map fun row => (row.map fun q => |(scaledEntry D q)|).sum).sum

/-- Positive entry upper bound `H = 2 * (shiftVal c).natAbs`. -/
private def HVal (c : BimatrixCode) : ℕ :=
  2 * (shiftVal c).natAbs

/-- Positive integer normalized payoff matrices `posMatWith D S M`. -/
private def posMatWith (D S : ℤ) (M : List (List ℚ)) : List (List ℤ) :=
  M.map fun row => row.map fun q => scaledEntry D q + S

/-- Positive integer normalized payoff matrices `posMat c M`. -/
private def posMat (c : BimatrixCode) (M : List (List ℚ)) : List (List ℤ) :=
  posMatWith (clearScale c) (shiftVal c) M

@[local fun_prop]
private theorem clearScale_polytime :
    ComputableInPolyTime clearScale encBimatrix encIntBin := by
  unfold clearScale
  fun_prop

@[local fun_prop]
private theorem scaledEntry_polytime {α : Type} {encIn : α ↪ List Bool}
    {D : α → ℤ} {q : α → ℚ}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hq : ComputableInPolyTime q encIn encRat) :
    ComputableInPolyTime (fun x => scaledEntry (D x) (q x)) encIn encIntBin := by
  unfold scaledEntry
  fun_prop

@[local fun_prop]
private theorem clearMat_polytime {α : Type} {encIn : α ↪ List Bool}
    {D : α → ℤ} {M : α → List (List ℚ)}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hM : ComputableInPolyTime M encIn (encList (encList encRat))) :
    ComputableInPolyTime (fun x => clearMat (D x) (M x)) encIn encIntTable := by
  have hrow : ComputableInPolyTime
      (fun p : ℤ × List ℚ => p.2.map (scaledEntry p.1))
      (encPair encIntBin (encList encRat)) (encList encIntBin) := by
    refine mapWithInput (encA := encRat) (snd _ _) ?_
    exact scaledEntry_polytime ((fst encIntBin (encList encRat)).comp (fst _ _)) (snd _ _)
  have hall : ComputableInPolyTime
      (fun x => (M x).map fun row => row.map (scaledEntry (D x)))
      encIn encIntTable := by
    refine mapWithInput (encA := encList encRat) hM ?_
    exact hrow.comp ((hD.comp (fst _ _)).prod (snd _ _))
  simpa only [clearMat] using hall

@[local fun_prop]
private theorem codeFst_polytime :
    ComputableInPolyTime (fun c : BimatrixCode => c.matA) encBimatrix
      (encList (encList encRat)) :=
  encBimatrix_matA_polyTime .id'

@[local fun_prop]
private theorem codeSnd_polytime :
    ComputableInPolyTime (fun c : BimatrixCode => c.matB) encBimatrix
      (encList (encList encRat)) :=
  encBimatrix_matB_polyTime .id'

@[local fun_prop]
private theorem codeRows_polytime :
    ComputableInPolyTime rows encBimatrix encUnary := by
  unfold rows
  exact (length_list _).comp codeFst_polytime

@[local fun_prop]
private theorem codeCols_polytime :
    ComputableInPolyTime cols encBimatrix encUnary := by
  unfold cols
  exact (length_list _).comp ((headD (encA := encList encRat) []).comp codeFst_polytime)

@[local fun_prop]
private theorem shiftVal_polytime :
    ComputableInPolyTime shiftVal encBimatrix encIntBin := by
  unfold shiftVal
  have habs : ∀ {α : Type} {encIn : α ↪ List Bool} {f : α → ℤ},
      ComputableInPolyTime f encIn encIntBin →
        ComputableInPolyTime (fun x => |f x|) encIn encIntBin := by
    intro α encIn f hf
    have hc : ComputableInPolyTime (fun x => ((f x).natAbs : ℤ)) encIn encIntBin := by fun_prop
    simpa only [Int.natCast_natAbs] using hc
  have hrow1 : ComputableInPolyTime
      (fun p : BimatrixCode × List ℚ => (p.2.map fun q => |scaledEntry (clearScale p.1) q|).sum)
      (encPair encBimatrix (encList encRat)) encIntBin := by
    refine intBin_sum.comp (mapWithInput (encA := encRat) (snd _ _) ?_)
    exact habs (scaledEntry_polytime
      (clearScale_polytime.comp ((fst _ _).comp (fst _ _))) (snd _ _))
  have hs1 : ComputableInPolyTime
      (fun c : BimatrixCode =>
        (c.matA.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum)
      encBimatrix encIntBin :=
    intBin_sum.comp (mapWithInput (encA := encList encRat) codeFst_polytime hrow1)
  have hs2 : ComputableInPolyTime
      (fun c : BimatrixCode =>
        (c.matB.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum)
      encBimatrix encIntBin :=
    intBin_sum.comp (mapWithInput (encA := encList encRat) codeSnd_polytime hrow1)
  exact intBin_add' (intBin_add' (const 1) hs1) hs2

@[local fun_prop]
private theorem wellFormedB_polytime :
    ComputableInPolyTime wellFormedB encBimatrix encBool := by
  have ha1 : ComputableInPolyTime
      (fun c : BimatrixCode => c.matA.all fun r => decide (r.length = c.cols))
      encBimatrix encBool := by
    refine allWithInput (encA := encList encRat) codeFst_polytime ?_
    exact decide_eq' ((length_list encRat).comp (snd _ _)) (codeCols_polytime.comp (fst _ _))
  have ha2 : ComputableInPolyTime
      (fun c : BimatrixCode => c.matB.all fun r => decide (r.length = c.cols))
      encBimatrix encBool := by
    refine allWithInput (encA := encList encRat) codeSnd_polytime ?_
    exact decide_eq' ((length_list encRat).comp (snd _ _)) (codeCols_polytime.comp (fst _ _))
  unfold wellFormedB
  fun_prop

@[local fun_prop]
private theorem HVal_polytime :
    ComputableInPolyTime HVal encBimatrix encNat := by
  unfold HVal
  fun_prop

private theorem posMatWith_polytime {α : Type} {encIn : α ↪ List Bool}
    {D S : α → ℤ} {M : α → List (List ℚ)}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hS : ComputableInPolyTime S encIn encIntBin)
    (hM : ComputableInPolyTime M encIn (encList (encList encRat))) :
    ComputableInPolyTime (fun x => posMatWith (D x) (S x) (M x)) encIn encIntTable := by
  have hrow : ComputableInPolyTime
      (fun p : (ℤ × ℤ) × List ℚ => p.2.map fun q => scaledEntry p.1.1 q + p.1.2)
      (encPair (encPair encIntBin encIntBin) (encList encRat)) (encList encIntBin) := by
    refine mapWithInput (encA := encRat) (snd _ _) ?_
    exact intBin_add'
      (scaledEntry_polytime ((fst encIntBin encIntBin).comp ((fst _ _).comp (fst _ _))) (snd _ _))
      ((snd encIntBin encIntBin).comp ((fst _ _).comp (fst _ _)))
  have hm : ComputableInPolyTime
      (fun x => (M x).map fun row => row.map fun q => scaledEntry (D x) q + S x)
      encIn encIntTable := by
    refine mapWithInput (encA := encList encRat) hM ?_
    exact hrow.comp (((hD.prod hS).comp (fst _ _)).prod (snd _ _))
  simpa only [posMatWith] using hm

private theorem posMatA_polytime :
    ComputableInPolyTime (fun c : BimatrixCode => posMat c c.matA) encBimatrix encIntTable :=
  posMatWith_polytime clearScale_polytime shiftVal_polytime codeFst_polytime

private theorem posMatB_polytime :
    ComputableInPolyTime (fun c : BimatrixCode => posMat c c.matB) encBimatrix encIntTable :=
  posMatWith_polytime clearScale_polytime shiftVal_polytime codeSnd_polytime

/-! ### Section 3: Exact FNP verifier -/

private def witnessDecoder : Decoder encWitnessPairs :=
  Decoder.pair (Decoder.list (Decoder.pair Decoder.intBin Decoder.nat))
    (Decoder.list (Decoder.pair Decoder.intBin Decoder.nat))

private def isCanonicalNonnegPair (pq : ℤ × ℕ) : Bool :=
  decide (0 ≤ pq.1) && decide (0 < pq.2) && decide (Nat.gcd pq.1.natAbs pq.2 = 1)

private def mkRatOfPair (pq : ℤ × ℕ) : ℚ :=
  (pq.1 : ℚ) / (pq.2 : ℚ)

private lemma mkRatOfPair_num_den {pq : ℤ × ℕ} (hc : isCanonicalNonnegPair pq = true) :
    (mkRatOfPair pq).num = pq.1 ∧ (mkRatOfPair pq).den = pq.2 := by
  simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hp, hq⟩, hgcd⟩
  have hr : mkRatOfPair pq = Rat.divInt pq.1 (pq.2 : ℤ) := by
    simp only [mkRatOfPair, ← Int.cast_natCast (R := ℚ), Rat.divInt_eq_div]
  have hsign : (pq.2 : ℤ).sign = 1 := Int.sign_eq_one_of_pos (by omega)
  have hgcdZ : (pq.2 : ℤ).gcd pq.1 = 1 := by
    change Nat.gcd pq.2 pq.1.natAbs = 1
    rw [Nat.gcd_comm]
    exact hgcd
  have hne : (pq.2 : ℤ) ≠ 0 := by omega
  have hnum : (mkRatOfPair pq).num = pq.1 := by
    rw [hr, Rat.num_divInt, hsign, hgcdZ, one_mul]
    change pq.1 / (1 : ℤ) = pq.1
    omega
  have hden : (mkRatOfPair pq).den = pq.2 := by
    rw [hr, Rat.den_divInt]
    simp only [hne, ite_false, Int.natAbs_natCast, hgcdZ, Nat.div_one]
  exact ⟨hnum, hden⟩

private lemma rat_isCanonical {q : ℚ} (hq : 0 ≤ q) :
    isCanonicalNonnegPair (q.num, q.den) = true := by
  simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨Rat.num_nonneg.2 hq, Nat.pos_of_ne_zero q.den_nz⟩, q.reduced⟩

private def scaleVecNum (D : ℤ) (v : List (ℤ × ℕ)) : List ℤ :=
  v.map fun pq => pq.1 * D.tdiv (pq.2 : ℤ)

private def transposeRows (m n : ℕ) (M : List (List ℤ)) : List (List ℤ) :=
  (List.range n).map fun j => (List.range m).map fun i => rowEntry M i j

private def rowPayoffs (M : List (List ℤ)) (k : ℕ) (v : List ℤ) : List ℤ :=
  M.map fun row => ListMatrix.dotProduct k row v

private def clearMatA (c : BimatrixCode) : List (List ℤ) := clearMat (clearScale c) c.matA
private def clearMatB (c : BimatrixCode) : List (List ℤ) := clearMat (clearScale c) c.matB

private def vecProdDen (v : List (ℤ × ℕ)) : ℤ := (v.map fun pq => (pq.2 : ℤ)).prod

private def pay1Vec (c : BimatrixCode) (yl : List (ℤ × ℕ)) : List ℤ :=
  rowPayoffs (clearMatA c) c.cols (scaleVecNum (vecProdDen yl) yl)

private def pay2Vec (c : BimatrixCode) (xl : List (ℤ × ℕ)) : List ℤ :=
  rowPayoffs (transposeRows c.rows c.cols (clearMatB c)) c.rows (scaleVecNum (vecProdDen xl) xl)

private def brCheck (D mix : ℤ) (pays : List ℤ) : Bool :=
  pays.all fun v => decide (D * v ≤ mix)

private def verifiesDecoded (c : BimatrixCode) (w : List Bool)
    (dec : List (ℤ × ℕ) × List (ℤ × ℕ)) : Bool :=
  decide (encWitnessPairs dec = w) &&
    decide (dec.1.length = c.rows) && decide (dec.2.length = c.cols) &&
    dec.1.all isCanonicalNonnegPair && dec.2.all isCanonicalNonnegPair &&
    decide ((scaleVecNum (vecProdDen dec.1) dec.1).sum = vecProdDen dec.1) &&
    decide ((scaleVecNum (vecProdDen dec.2) dec.2).sum = vecProdDen dec.2) &&
    brCheck (vecProdDen dec.1)
      (ListMatrix.dotProduct c.rows (scaleVecNum (vecProdDen dec.1) dec.1) (pay1Vec c dec.2))
      (pay1Vec c dec.2) &&
    brCheck (vecProdDen dec.2)
      (ListMatrix.dotProduct c.cols (scaleVecNum (vecProdDen dec.2) dec.2) (pay2Vec c dec.1))
      (pay2Vec c dec.1)

private def verifiesBimatrixNash (p : BimatrixCode × List Bool) : Bool :=
  if !p.1.wellFormedB then p.2.isEmpty
  else verifiesDecoded p.1 p.2 (witnessDecoder.decode p.2)

@[local fun_prop]
private theorem witnessDecoder_polytime :
    ComputableInPolyTime witnessDecoder.decode encBits encWitnessPairs :=
  witnessDecoder.computableInPolyTime

@[local fun_prop]
private theorem isCanonicalNonnegPair_polytime :
    ComputableInPolyTime isCanonicalNonnegPair encRatData encBool := by
  unfold isCanonicalNonnegPair
  fun_prop

@[local fun_prop]
private theorem vecProdDen_polytime {α : Type} {encIn : α ↪ List Bool}
    {v : α → List (ℤ × ℕ)} (hv : ComputableInPolyTime v encIn (encList encRatData)) :
    ComputableInPolyTime (fun x => vecProdDen (v x)) encIn encIntBin := by
  unfold vecProdDen
  fun_prop

@[local fun_prop]
private theorem scaleVecNum_polytime {α : Type} {encIn : α ↪ List Bool}
    {D : α → ℤ} {v : α → List (ℤ × ℕ)}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hv : ComputableInPolyTime v encIn (encList encRatData)) :
    ComputableInPolyTime (fun x => scaleVecNum (D x) (v x)) encIn (encList encIntBin) := by
  unfold scaleVecNum
  refine mapWithInput (encA := encRatData) hv ?_
  exact intBin_mul' ((fst encIntBin encNat).comp (snd _ _))
    (intBin_tdiv' (hD.comp (fst _ _))
      (intBin_natCast.comp ((snd encIntBin encNat).comp (snd _ _))))

@[local fun_prop]
private theorem transposeRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {m n : α → ℕ} {M : α → List (List ℤ)}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hn : ComputableInPolyTime n encIn encUnary)
    (hM : ComputableInPolyTime M encIn encIntTable) :
    ComputableInPolyTime (fun x => transposeRows (m x) (n x) (M x)) encIn encIntTable := by
  have hcol : ComputableInPolyTime
      (fun p : α × ℕ => (List.range (m p.1)).map fun i => rowEntry (M p.1) i p.2)
      (encPair encIn encUnary) (encList encIntBin) := by
    refine mapWithInput (encA := encUnary) (range.comp (hm.comp (fst _ _))) ?_
    exact computableInPolyTime_rowEntry (hM.comp ((fst _ _).comp (fst _ _)))
      (snd _ _) ((snd _ _).comp (fst _ _))
  unfold transposeRows
  refine mapWithInput (encA := encUnary) ?_ ?_
  · exact range.comp hn
  · exact hcol

@[local fun_prop]
private theorem rowPayoffs_polytime {α : Type} {encIn : α ↪ List Bool}
    {M : α → List (List ℤ)} {k : α → ℕ} {v : α → List ℤ}
    (hM : ComputableInPolyTime M encIn encIntTable)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => rowPayoffs (M x) (k x) (v x)) encIn (encList encIntBin) := by
  unfold rowPayoffs
  refine mapWithInput (encA := encList encIntBin) hM ?_
  exact listDotProduct.comp ((hk.comp (fst _ _)).prod ((snd _ _).prod (hv.comp (fst _ _))))

@[local fun_prop]
private theorem clearMatA_polytime :
    ComputableInPolyTime clearMatA encBimatrix encIntTable := by
  unfold clearMatA
  exact clearMat_polytime clearScale_polytime codeFst_polytime

@[local fun_prop]
private theorem clearMatB_polytime :
    ComputableInPolyTime clearMatB encBimatrix encIntTable := by
  unfold clearMatB
  exact clearMat_polytime clearScale_polytime codeSnd_polytime

@[local fun_prop]
private theorem pay1Vec_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {yl : α → List (ℤ × ℕ)}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (hyl : ComputableInPolyTime yl encIn (encList encRatData)) :
    ComputableInPolyTime (fun x => pay1Vec (c x) (yl x)) encIn (encList encIntBin) := by
  unfold pay1Vec
  exact rowPayoffs_polytime (clearMatA_polytime.comp hc) (codeCols_polytime.comp hc)
    (scaleVecNum_polytime (vecProdDen_polytime hyl) hyl)

@[local fun_prop]
private theorem pay2Vec_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {xl : α → List (ℤ × ℕ)}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (hxl : ComputableInPolyTime xl encIn (encList encRatData)) :
    ComputableInPolyTime (fun x => pay2Vec (c x) (xl x)) encIn (encList encIntBin) := by
  unfold pay2Vec
  exact rowPayoffs_polytime
    (transposeRows_polytime (codeRows_polytime.comp hc) (codeCols_polytime.comp hc)
      (clearMatB_polytime.comp hc))
    (codeRows_polytime.comp hc)
    (scaleVecNum_polytime (vecProdDen_polytime hxl) hxl)

@[local fun_prop]
private theorem brCheck_polytime {α : Type} {encIn : α ↪ List Bool}
    {D mix : α → ℤ} {pays : α → List ℤ}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hmix : ComputableInPolyTime mix encIn encIntBin)
    (hpays : ComputableInPolyTime pays encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => brCheck (D x) (mix x) (pays x)) encIn encBool := by
  unfold brCheck
  refine allWithInput (encA := encIntBin) hpays ?_
  exact intBin_le' (intBin_mul' (hD.comp (fst _ _)) (snd _ _)) (hmix.comp (fst _ _))

private theorem verifiesDecoded_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {w : α → List Bool} {dec : α → List (ℤ × ℕ) × List (ℤ × ℕ)}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (hw : ComputableInPolyTime w encIn encBits)
    (hdec : ComputableInPolyTime dec encIn encWitnessPairs) :
    ComputableInPolyTime (fun x => verifiesDecoded (c x) (w x) (dec x)) encIn encBool := by
  have hreenc : ComputableInPolyTime (fun x => encWitnessPairs (dec x)) encIn encBits :=
    (of_eq (f := fun z => encWitnessPairs z) (encIn := encWitnessPairs)
      (encOut := encBits) fun _ => rfl).comp hdec
  have hxl : ComputableInPolyTime (fun x => (dec x).1) encIn (encList encRatData) :=
    (fst _ _).comp hdec
  have hyl : ComputableInPolyTime (fun x => (dec x).2) encIn (encList encRatData) :=
    (snd _ _).comp hdec
  have hDx := vecProdDen_polytime hxl
  have hDy := vecProdDen_polytime hyl
  have hxs := scaleVecNum_polytime hDx hxl
  have hys := scaleVecNum_polytime hDy hyl
  have hp1 := pay1Vec_polytime hc hyl
  have hp2 := pay2Vec_polytime hc hxl
  have hm1 : ComputableInPolyTime
      (fun x => ListMatrix.dotProduct (c x).rows
        (scaleVecNum (vecProdDen (dec x).1) (dec x).1) (pay1Vec (c x) (dec x).2))
      encIn encIntBin := listDotProduct.comp ((codeRows_polytime.comp hc).prod (hxs.prod hp1))
  have hm2 : ComputableInPolyTime
      (fun x => ListMatrix.dotProduct (c x).cols
        (scaleVecNum (vecProdDen (dec x).2) (dec x).2) (pay2Vec (c x) (dec x).1))
      encIn encIntBin := listDotProduct.comp ((codeCols_polytime.comp hc).prod (hys.prod hp2))
  have ha1 : ComputableInPolyTime
      (fun x => (dec x).1.all isCanonicalNonnegPair) encIn encBool := by
    refine allWithInput (encA := encRatData) hxl ?_
    exact isCanonicalNonnegPair_polytime.comp (snd _ _)
  have ha2 : ComputableInPolyTime
      (fun x => (dec x).2.all isCanonicalNonnegPair) encIn encBool := by
    refine allWithInput (encA := encRatData) hyl ?_
    exact isCanonicalNonnegPair_polytime.comp (snd _ _)
  unfold verifiesDecoded
  refine bool_and' ?_ (brCheck_polytime hDy hm2 hp2)
  refine bool_and' ?_ (brCheck_polytime hDx hm1 hp1)
  refine bool_and' ?_ (decide_eq' (intBin_sum.comp hys) hDy)
  refine bool_and' ?_ (decide_eq' (intBin_sum.comp hxs) hDx)
  refine bool_and' ?_ ha2
  refine bool_and' ?_ ha1
  refine bool_and' ?_ (decide_eq' ((length_list encRatData).comp hyl) (codeCols_polytime.comp hc))
  exact bool_and' (decide_eq' hreenc hw)
    (decide_eq' ((length_list encRatData).comp hxl) (codeRows_polytime.comp hc))

private theorem verifiesBimatrixNash_polytime :
    ComputableInPolyTime verifiesBimatrixNash (encPair encBimatrix encBits) encBool := by
  have hdec := verifiesDecoded_polytime (fst encBimatrix encBits) (snd encBimatrix encBits)
    (witnessDecoder_polytime.comp (snd encBimatrix encBits))
  have hi := ite' (bool_not.comp (wellFormedB_polytime.comp (fst encBimatrix encBits)))
    (bitsIsEmpty.comp (snd encBimatrix encBits)) hdec
  exact hi.of_enc_eq (encD := encBool) fun p => by
    simp only [verifiesBimatrixNash, Function.comp_apply]

private lemma encWitness_eq_pairs (x y : List ℚ) :
    encWitness ⟨x, y⟩ =
      encWitnessPairs (x.map (fun q => (q.num, q.den)), y.map (fun q => (q.num, q.den))) := by
  have hmap : ∀ l : List ℚ,
      encList encRat l = encList encRatData (l.map fun q => (q.num, q.den)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [encList_cons, List.map_cons, ih, encRat_apply]
  rw [encWitness_apply]
  simp only [encPair_apply, hmap]

private lemma dotProduct_eq_fin_sum (k : ℕ) (a b : List ℤ) :
    ListMatrix.dotProduct k a b = ∑ i : Fin k, a.getD i.1 0 * b.getD i.1 0 := by
  rw [ListMatrix.dotProduct_eq_sum_map_range, List.sum_map_range]

private lemma clearScale_pos (c : BimatrixCode) : 0 < clearScale c := by
  have hprod : ∀ M : List (List ℚ),
      0 < (M.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod := by
    intro M
    induction M with
    | nil => simp
    | cons r M ih =>
      simp only [List.map_cons, List.prod_cons]
      refine mul_pos ?_ ih
      clear ih
      induction r with
      | nil => simp
      | cons q r ih =>
        simp only [List.map_cons, List.prod_cons]
        exact mul_pos (Int.natCast_pos.2 q.den_pos) ih
  exact mul_pos (hprod c.matA) (hprod c.matB)

private lemma den_dvd_clearScale {c : BimatrixCode} {M : List (List ℚ)}
    (hM : M = c.matA ∨ M = c.matB) {r : List ℚ} (hr : r ∈ M) {q : ℚ} (hq : q ∈ r) :
    (q.den : ℤ) ∣ clearScale c := by
  have hdvd_row : (q.den : ℤ) ∣ (r.map fun q => (q.den : ℤ)).prod := by
    have hmem : (q.den : ℤ) ∈ r.map fun q => (q.den : ℤ) := List.mem_map.2 ⟨q, hq, rfl⟩
    exact List.dvd_prod hmem
  have hdvd_mat : (r.map fun q => (q.den : ℤ)).prod ∣
      (M.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod :=
    List.dvd_prod (List.mem_map.2 ⟨r, hr, rfl⟩)
  have hdvd : (q.den : ℤ) ∣ (M.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod :=
    hdvd_row.trans hdvd_mat
  rcases hM with rfl | rfl
  · exact dvd_mul_of_dvd_left hdvd _
  · exact dvd_mul_of_dvd_right hdvd _

private lemma scaledEntry_cast {D : ℤ} {q : ℚ} (hdvd : (q.den : ℤ) ∣ D) :
    ((scaledEntry D q : ℤ) : ℚ) = (D : ℚ) * q := by
  rcases hdvd with ⟨k, hk⟩
  have hneZ : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have hneQ : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have htdiv : D.tdiv (q.den : ℤ) = k := by
    rw [hk, Int.mul_tdiv_cancel_left k hneZ]
  have hDk : (D : ℚ) = (q.den : ℚ) * (k : ℚ) := by exact_mod_cast hk
  have hq : (q.num : ℚ) = q * (q.den : ℚ) := by
    have hmul := congrArg (· * (q.den : ℚ)) (Rat.num_div_den q)
    rw [div_mul_cancel₀ _ hneQ] at hmul
    exact hmul
  simp only [scaledEntry, htdiv, Int.cast_mul, hDk, hq]
  ring

private lemma list_getD_map_lt {α β : Type*} (f : α → β) (l : List α) (d₀ : α) (d₁ : β)
    {i : ℕ} (hi : i < l.length) :
    (l.map f).getD i d₁ = f (l.getD i d₀) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

private lemma clearMat_getD_cast {c : BimatrixCode} (hc : c.WellFormed)
    (i : Fin c.rows) (j : Fin c.cols) :
    (((clearMatA c).getD i.1 []).getD j.1 0 : ℚ) = (clearScale c : ℚ) * c.toMatA i j ∧
      (((clearMatB c).getD i.1 []).getD j.1 0 : ℚ) = (clearScale c : ℚ) * c.toMatB i j := by
  obtain ⟨_, _, hl2, hr1, hr2⟩ := hc
  have aux : ∀ (M : List (List ℚ)) (hM : M = c.matA ∨ M = c.matB)
      (hlen : M.length = c.rows) (hrows : ∀ r ∈ M, r.length = c.cols),
      (((clearMat (clearScale c) M).getD i.1 []).getD j.1 0 : ℚ) =
        (clearScale c : ℚ) * (M.getD i.1 []).getD j.1 0 := by
    intro M hM hlen hrows
    have hi : i.1 < M.length := by rw [hlen]; exact i.2
    have hrmem : M.getD i.1 [] ∈ M := List.getD_mem [] hi
    have hrlen : (M.getD i.1 []).length = c.cols := hrows _ hrmem
    have hj : j.1 < (M.getD i.1 []).length := by rw [hrlen]; exact j.2
    have hqmem : (M.getD i.1 []).getD j.1 0 ∈ M.getD i.1 [] := List.getD_mem 0 hj
    have h1 : (clearMat (clearScale c) M).getD i.1 [] =
        (M.getD i.1 []).map (scaledEntry (clearScale c)) :=
      list_getD_map_lt (List.map (scaledEntry (clearScale c))) M [] [] hi
    have h2 : ((clearMat (clearScale c) M).getD i.1 []).getD j.1 0 =
        scaledEntry (clearScale c) ((M.getD i.1 []).getD j.1 0) := by
      rw [h1]
      exact list_getD_map_lt (scaledEntry (clearScale c)) (M.getD i.1 []) 0 0 hj
    rw [h2]
    exact scaledEntry_cast (den_dvd_clearScale hM hrmem hqmem)
  exact ⟨aux c.matA (Or.inl rfl) rfl hr1, aux c.matB (Or.inr rfl) hl2 hr2⟩

private lemma vecProdDen_pos {v : List (ℤ × ℕ)} (hv : v.all isCanonicalNonnegPair = true) :
    0 < vecProdDen v := by
  rw [List.all_eq_true] at hv
  unfold vecProdDen
  induction v with
  | nil => simp
  | cons pq v ih =>
    have hpq := hv pq (by simp)
    simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hpq
    simp only [List.map_cons, List.prod_cons]
    exact mul_pos (by omega) (ih fun z hz => hv z (by simp [hz]))

private lemma den_dvd_vecProdDen {v : List (ℤ × ℕ)} {pq : ℤ × ℕ} (hpq : pq ∈ v) :
    (pq.2 : ℤ) ∣ vecProdDen v := by
  unfold vecProdDen
  exact List.dvd_prod (List.mem_map.2 ⟨pq, hpq, rfl⟩)

private lemma scaleVecNum_getD_cast {v : List (ℤ × ℕ)} (hv : v.all isCanonicalNonnegPair = true)
    {k : ℕ} (hk : v.length = k) (i : Fin k) :
    ((scaleVecNum (vecProdDen v) v).getD i.1 0 : ℚ) =
      (vecProdDen v : ℚ) * (v.map mkRatOfPair).getD i.1 0 := by
  have hi : i.1 < v.length := by rw [hk]; exact i.2
  have hpq : v.getD i.1 (0, 0) ∈ v := List.getD_mem (0, 0) hi
  have hmem := (List.all_eq_true.1 hv) _ hpq
  simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hmem
  have hdvd := den_dvd_vecProdDen hpq
  rcases hdvd with ⟨t, ht⟩
  have hneZ : ((v.getD i.1 (0, 0)).2 : ℤ) ≠ 0 := by omega
  have hneQ : ((v.getD i.1 (0, 0)).2 : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : (v.getD i.1 (0, 0)).2 ≠ 0)
  have hget1 : (scaleVecNum (vecProdDen v) v).getD i.1 0 =
      (v.getD i.1 (0, 0)).1 * (vecProdDen v).tdiv ((v.getD i.1 (0, 0)).2 : ℤ) :=
    list_getD_map_lt _ v (0, 0) 0 hi
  have hget2 : (v.map mkRatOfPair).getD i.1 0 = mkRatOfPair (v.getD i.1 (0, 0)) :=
    list_getD_map_lt mkRatOfPair v (0, 0) 0 hi
  rw [hget1, hget2]
  have htdiv : (vecProdDen v).tdiv ((v.getD i.1 (0, 0)).2 : ℤ) = t := by
    rw [ht, Int.mul_tdiv_cancel_left t hneZ]
  have hvt : (vecProdDen v : ℚ) = ((v.getD i.1 (0, 0)).2 : ℚ) * (t : ℚ) := by exact_mod_cast ht
  simp only [htdiv, mkRatOfPair, Int.cast_mul, hvt]
  field_simp [hneQ]

private lemma pay1Vec_getD_cast {c : BimatrixCode} (hc : c.WellFormed)
    {yl : List (ℤ × ℕ)} (hyl_c : yl.all isCanonicalNonnegPair = true) (hyl_len : yl.length = c.cols)
    (i : Fin c.rows) :
    ((pay1Vec c yl).getD i.1 0 : ℚ) =
      (clearScale c : ℚ) * (vecProdDen yl : ℚ) *
        ∑ j : Fin c.cols, c.toMatA i j * (yl.map mkRatOfPair).getD j.1 0 := by
  have hlen : (clearMatA c).length = c.rows := by simp [clearMatA, clearMat, rows]
  have hi : i.1 < (clearMatA c).length := by rw [hlen]; exact i.2
  have hget : (pay1Vec c yl).getD i.1 0 =
      ListMatrix.dotProduct c.cols ((clearMatA c).getD i.1 [])
        (scaleVecNum (vecProdDen yl) yl) :=
    list_getD_map_lt _ (clearMatA c) [] 0 hi
  rw [hget, dotProduct_eq_fin_sum]
  push_cast
  calc
    ∑ j : Fin c.cols,
        (((clearMatA c).getD i.1 []).getD j.1 0 : ℚ) *
          ((scaleVecNum (vecProdDen yl) yl).getD j.1 0 : ℚ)
      = ∑ j : Fin c.cols,
          ((clearScale c : ℚ) * c.toMatA i j) *
            ((vecProdDen yl : ℚ) * (yl.map mkRatOfPair).getD j.1 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [(clearMat_getD_cast hc i j).1, scaleVecNum_getD_cast hyl_c hyl_len j]
    _ = (clearScale c : ℚ) * (vecProdDen yl : ℚ) *
          ∑ j : Fin c.cols, c.toMatA i j * (yl.map mkRatOfPair).getD j.1 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring

private lemma pay2Vec_getD_cast {c : BimatrixCode} (hc : c.WellFormed)
    {xl : List (ℤ × ℕ)} (hxl_c : xl.all isCanonicalNonnegPair = true) (hxl_len : xl.length = c.rows)
    (j : Fin c.cols) :
    ((pay2Vec c xl).getD j.1 0 : ℚ) =
      (clearScale c : ℚ) * (vecProdDen xl : ℚ) *
        ∑ i : Fin c.rows, (xl.map mkRatOfPair).getD i.1 0 * c.toMatB i j := by
  have hlen : (transposeRows c.rows c.cols (clearMatB c)).length = c.cols := by
    simp [transposeRows]
  have hj : j.1 < (transposeRows c.rows c.cols (clearMatB c)).length := by rw [hlen]; exact j.2
  have hget : (pay2Vec c xl).getD j.1 0 =
      ListMatrix.dotProduct c.rows
        ((transposeRows c.rows c.cols (clearMatB c)).getD j.1 [])
        (scaleVecNum (vecProdDen xl) xl) :=
    list_getD_map_lt
      (fun row => ListMatrix.dotProduct c.rows row (scaleVecNum (vecProdDen xl) xl))
      (transposeRows c.rows c.cols (clearMatB c)) [] 0 hj
  have htr : ∀ i : Fin c.rows,
      (((transposeRows c.rows c.cols (clearMatB c)).getD j.1 []).getD i.1 0) =
        ((clearMatB c).getD i.1 []).getD j.1 0 := fun i => by
    simp only [transposeRows]
    rw [List.getD_map_range _ [] j.2, List.getD_map_range _ 0 i.2]
    rfl
  rw [hget, dotProduct_eq_fin_sum]
  push_cast
  calc
    ∑ i : Fin c.rows,
        ((((transposeRows c.rows c.cols (clearMatB c)).getD j.1 []).getD i.1 0 : ℤ) : ℚ) *
          ((scaleVecNum (vecProdDen xl) xl).getD i.1 0 : ℚ)
      = ∑ i : Fin c.rows,
          ((clearScale c : ℚ) * c.toMatB i j) *
            ((vecProdDen xl : ℚ) * (xl.map mkRatOfPair).getD i.1 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [htr i, (clearMat_getD_cast hc i j).2, scaleVecNum_getD_cast hxl_c hxl_len i]
    _ = (clearScale c : ℚ) * (vecProdDen xl : ℚ) *
          ∑ i : Fin c.rows, (xl.map mkRatOfPair).getD i.1 0 * c.toMatB i j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring

private lemma brCheck_iff {D mix : ℤ} {pays : List ℤ} {k : ℕ} (hk : pays.length = k) :
    brCheck D mix pays = true ↔ ∀ i : Fin k, D * pays.getD i.1 0 ≤ mix := by
  simp only [brCheck, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    exact h _ (List.getD_mem 0 (by omega))
  · intro h v hv
    rcases List.mem_iff_getElem.1 hv with ⟨i, hi, rfl⟩
    have hi' : i < k := by omega
    simpa only [List.getD_eq_getElem pays 0 hi] using h ⟨i, hi'⟩

private lemma bilinear_dotProduct_eq_cast {m n : ℕ} (xl yl : List (ℤ × ℕ)) (pv : List ℤ)
    (C : ℚ) (M : Fin m → Fin n → ℚ)
    (hxl_c : xl.all isCanonicalNonnegPair = true) (hxl_len : xl.length = m)
    (hpv : ∀ a : Fin m, (pv.getD a.1 0 : ℚ) =
      C * (vecProdDen yl : ℚ) * ∑ j : Fin n, M a j * (yl.map mkRatOfPair).getD j.1 0) :
    ((ListMatrix.dotProduct m (scaleVecNum (vecProdDen xl) xl) pv : ℤ) : ℚ) =
      (vecProdDen xl : ℚ) * C * (vecProdDen yl : ℚ) *
        ∑ a : Fin m, ∑ j : Fin n,
          (xl.map mkRatOfPair).getD a.1 0 * M a j * (yl.map mkRatOfPair).getD j.1 0 := by
  rw [dotProduct_eq_fin_sum]
  push_cast
  calc
    ∑ a : Fin m, ((scaleVecNum (vecProdDen xl) xl).getD a.1 0 : ℚ) * (pv.getD a.1 0 : ℚ)
      = ∑ a : Fin m, ((vecProdDen xl : ℚ) * (xl.map mkRatOfPair).getD a.1 0) *
          (C * (vecProdDen yl : ℚ) *
            ∑ j : Fin n, M a j * (yl.map mkRatOfPair).getD j.1 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [scaleVecNum_getD_cast hxl_c hxl_len a, hpv a]
    _ = (vecProdDen xl : ℚ) * C * (vecProdDen yl : ℚ) *
          ∑ a : Fin m, ∑ j : Fin n,
            (xl.map mkRatOfPair).getD a.1 0 * M a j * (yl.map mkRatOfPair).getD j.1 0 := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

private lemma mix1_eq_cast {c : BimatrixCode} (hc : c.WellFormed)
    {xl yl : List (ℤ × ℕ)} (hxl_c : xl.all isCanonicalNonnegPair = true)
    (hyl_c : yl.all isCanonicalNonnegPair = true)
    (hxl_len : xl.length = c.rows) (hyl_len : yl.length = c.cols) :
    ((ListMatrix.dotProduct c.rows (scaleVecNum (vecProdDen xl) xl)
        (pay1Vec c yl) : ℤ) : ℚ) =
      (vecProdDen xl : ℚ) * (clearScale c : ℚ) * (vecProdDen yl : ℚ) *
        ∑ a : Fin c.rows, ∑ j : Fin c.cols,
          (xl.map mkRatOfPair).getD a.1 0 * c.toMatA a j * (yl.map mkRatOfPair).getD j.1 0 :=
  bilinear_dotProduct_eq_cast xl yl (pay1Vec c yl) (clearScale c) c.toMatA
    hxl_c hxl_len (pay1Vec_getD_cast hc hyl_c hyl_len)

private lemma mix2_eq_cast {c : BimatrixCode} (hc : c.WellFormed)
    {xl yl : List (ℤ × ℕ)} (hxl_c : xl.all isCanonicalNonnegPair = true)
    (hyl_c : yl.all isCanonicalNonnegPair = true)
    (hxl_len : xl.length = c.rows) (hyl_len : yl.length = c.cols) :
    ((ListMatrix.dotProduct c.cols (scaleVecNum (vecProdDen yl) yl)
        (pay2Vec c xl) : ℤ) : ℚ) =
      (vecProdDen yl : ℚ) * (clearScale c : ℚ) * (vecProdDen xl : ℚ) *
        ∑ i : Fin c.rows, ∑ b : Fin c.cols,
          (xl.map mkRatOfPair).getD i.1 0 * c.toMatB i b * (yl.map mkRatOfPair).getD b.1 0 := by
  rw [bilinear_dotProduct_eq_cast yl xl (pay2Vec c xl) (clearScale c) (fun b i => c.toMatB i b)
      hyl_c hyl_len (fun b => by
        rw [pay2Vec_getD_cast hc hxl_c hxl_len b]
        refine congrArg _ (Finset.sum_congr rfl fun i _ => mul_comm _ _)),
      Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring)

private lemma all_mkRatOfPair_nonneg {l : List (ℤ × ℕ)}
    (hl : l.all isCanonicalNonnegPair = true) : ∀ q ∈ l.map mkRatOfPair, 0 ≤ q := by
  intro q hq
  rcases List.mem_map.1 hq with ⟨pq, hpq, rfl⟩
  have hpqc := (List.all_eq_true.1 hl) pq hpq
  simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hpqc
  exact div_nonneg (by exact_mod_cast hpqc.1.1) (by exact_mod_cast Nat.zero_le pq.2)

private lemma sum_map_mkRatOfPair_eq_one {n : ℕ} {l : List (ℤ × ℕ)}
    (hl_c : l.all isCanonicalNonnegPair = true) (hl_len : l.length = n)
    (hsum : (scaleVecNum (vecProdDen l) l).sum = vecProdDen l) :
    (l.map mkRatOfPair).sum = 1 := by
  have hD : (0 : ℚ) < (vecProdDen l : ℚ) := by exact_mod_cast vecProdDen_pos hl_c
  have hsQ : ((scaleVecNum (vecProdDen l) l).sum : ℚ) = (vecProdDen l : ℚ) := by
    exact_mod_cast hsum
  rw [← fin_sum_getD_eq_list_sum (scaleVecNum (vecProdDen l) l) 0
    (n := n) (by simp [scaleVecNum, hl_len])] at hsQ
  push_cast at hsQ
  have hsum' : ∑ i : Fin n, (vecProdDen l : ℚ) * (l.map mkRatOfPair).getD i.1 0 =
      (vecProdDen l : ℚ) := by
    have hcongr : ∑ i : Fin n, ((scaleVecNum (vecProdDen l) l).getD i.1 0 : ℚ) =
        ∑ i : Fin n, (vecProdDen l : ℚ) * (l.map mkRatOfPair).getD i.1 0 :=
      Finset.sum_congr rfl fun i _ => scaleVecNum_getD_cast hl_c hl_len i
    exact hcongr.symm.trans hsQ
  rw [← Finset.mul_sum] at hsum'
  have hfin : ∑ i : Fin n, (l.map mkRatOfPair).getD i.1 0 = 1 :=
    mul_left_cancel₀ hD.ne' (by simpa only [mul_one] using hsum')
  rw [← fin_sum_getD_eq_list_sum (l.map mkRatOfPair) 0 (n := n) (by simp [hl_len]), hfin]

private lemma list_sum_eq_one_of_div {k : ℕ} {v : List ℚ} {num : List ℤ}
    (hv_len : v.length = k) (hnum_len : num.length = k) (hpos : 0 < num.sum)
    (hget : ∀ i : Fin k, v.getD i.1 0 = (num.getD i.1 0 : ℚ) / (num.sum : ℚ)) :
    v.sum = 1 := by
  rw [← fin_sum_getD_eq_list_sum v 0 hv_len]
  have hne0 : (num.sum : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  calc ∑ i : Fin k, v.getD i.1 0
      = ∑ i : Fin k, (num.getD i.1 0 : ℚ) / (num.sum : ℚ) :=
        Finset.sum_congr rfl fun i _ => hget i
    _ = (∑ i : Fin k, (num.getD i.1 0 : ℚ)) / (num.sum : ℚ) := by rw [Finset.sum_div]
    _ = (num.sum : ℚ) / (num.sum : ℚ) := by
        rw [← Int.cast_sum, fin_sum_getD_eq_list_sum num 0 hnum_len]
    _ = 1 := div_self hne0

private lemma scaleVecNum_sum_eq_vecProdDen_of_sum_eq_one {n : ℕ} {l : List (ℤ × ℕ)}
    (hl_c : l.all isCanonicalNonnegPair = true) (hl_len : l.length = n)
    (hsum : (l.map mkRatOfPair).sum = 1) :
    (scaleVecNum (vecProdDen l) l).sum = vecProdDen l := by
  have hq : ((scaleVecNum (vecProdDen l) l).sum : ℚ) = (vecProdDen l : ℚ) := by
    rw [← fin_sum_getD_eq_list_sum (scaleVecNum (vecProdDen l) l) 0
      (n := n) (by simp [scaleVecNum, hl_len])]
    push_cast
    have hsum' : ∑ i : Fin n, ((scaleVecNum (vecProdDen l) l).getD i.1 0 : ℚ) =
        (vecProdDen l : ℚ) * ∑ i : Fin n, (l.map mkRatOfPair).getD i.1 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => scaleVecNum_getD_cast hl_c hl_len i
    rw [hsum', fin_sum_getD_eq_list_sum (l.map mkRatOfPair) 0 (n := n) (by simp [hl_len]),
      hsum, mul_one]
  exact_mod_cast hq

private lemma map_pair_mkRatOfPair_eq {l : List (ℤ × ℕ)}
    (hl : l.all isCanonicalNonnegPair = true) :
    (l.map mkRatOfPair).map (fun q => (q.num, q.den)) = l := by
  rw [List.map_map]
  have hm : List.map ((fun q : ℚ => (q.num, q.den)) ∘ mkRatOfPair) l = List.map id l := by
    refine List.map_congr_left fun pq hpq => ?_
    have hmk := mkRatOfPair_num_den ((List.all_eq_true.1 hl) pq hpq)
    exact Prod.ext hmk.1 hmk.2
  simpa only [List.map_id] using hm

private lemma all_isCanonicalNonnegPair_of_nonneg {l : List ℚ} (hl : ∀ q ∈ l, 0 ≤ q) :
    (l.map fun q => (q.num, q.den)).all isCanonicalNonnegPair = true := by
  rw [List.all_eq_true]
  intro pq hpq
  rcases List.mem_map.1 hpq with ⟨q, hq, rfl⟩
  exact rat_isCanonical (hl q hq)

private lemma map_mkRatOfPair_pair_eq (l : List ℚ) :
    (l.map fun q => (q.num, q.den)).map mkRatOfPair = l := by
  rw [List.map_map]
  have hm : List.map (mkRatOfPair ∘ fun q : ℚ => (q.num, q.den)) l = List.map id l := by
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply, mkRatOfPair, Rat.num_div_den, id_eq]
  simpa only [List.map_id] using hm

private lemma verifiesDecoded_iff {c : BimatrixCode} (hc : c.WellFormed)
    (w : List Bool) (dec : List (ℤ × ℕ) × List (ℤ × ℕ)) :
    verifiesDecoded c w dec = true ↔
      w = encWitnessPairs dec ∧
        dec.1.all isCanonicalNonnegPair = true ∧
        dec.2.all isCanonicalNonnegPair = true ∧
        c.IsRationalNash (dec.1.map mkRatOfPair) (dec.2.map mkRatOfPair) := by
  let x := dec.1.map mkRatOfPair
  let y := dec.2.map mkRatOfPair
  have hlenA : (pay1Vec c dec.2).length = c.rows := by
    simp [pay1Vec, rowPayoffs, clearMatA, clearMat, rows]
  have hlenB : (pay2Vec c dec.1).length = c.cols := by
    simp [pay2Vec, rowPayoffs, transposeRows]
  constructor
  · intro h
    simp only [verifiesDecoded, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hew, hdx⟩, hdy⟩, hcx⟩, hcy⟩, hsx⟩, hsy⟩, hb1⟩, hb2⟩
    refine ⟨hew.symm, hcx, hcy, ?_⟩
    have hDx : (0 : ℚ) < (vecProdDen dec.1 : ℚ) := by exact_mod_cast vecProdDen_pos hcx
    have hDy : (0 : ℚ) < (vecProdDen dec.2 : ℚ) := by exact_mod_cast vecProdDen_pos hcy
    have hDc : (0 : ℚ) < (clearScale c : ℚ) := by exact_mod_cast clearScale_pos c
    have hxlen : x.length = c.rows := by simp [x, hdx]
    have hylen : y.length = c.cols := by simp [y, hdy]
    have hxnn : ∀ q ∈ x, 0 ≤ q := all_mkRatOfPair_nonneg hcx
    have hynn : ∀ q ∈ y, 0 ≤ q := all_mkRatOfPair_nonneg hcy
    have hxsum : x.sum = 1 := sum_map_mkRatOfPair_eq_one hcx hdx hsx
    have hysum : y.sum = 1 := sum_map_mkRatOfPair_eq_one hcy hdy hsy
    have hmix1 := mix1_eq_cast hc hcx hcy hdx hdy
    have hmix2 := mix2_eq_cast hc hcx hcy hdx hdy
    have hpos1 : (0 : ℚ) < (vecProdDen dec.1 : ℚ) * (clearScale c : ℚ) * (vecProdDen dec.2 : ℚ) :=
      mul_pos (mul_pos hDx hDc) hDy
    have hpos2 : (0 : ℚ) < (vecProdDen dec.2 : ℚ) * (clearScale c : ℚ) * (vecProdDen dec.1 : ℚ) :=
      mul_pos (mul_pos hDy hDc) hDx
    have hbr1 : ∀ i : Fin c.rows,
        (∑ j : Fin c.cols, c.toMatA i j * y.getD j.1 0) ≤
          ∑ a : Fin c.rows, ∑ j : Fin c.cols, x.getD a.1 0 * c.toMatA a j * y.getD j.1 0 := by
      intro i
      have hiZ := (brCheck_iff hlenA).1 hb1 i
      have hiQ : ((vecProdDen dec.1 : ℤ) : ℚ) * ((pay1Vec c dec.2).getD i.1 0 : ℚ) ≤
          ((ListMatrix.dotProduct c.rows (scaleVecNum (vecProdDen dec.1) dec.1)
            (pay1Vec c dec.2) : ℤ) : ℚ) := by exact_mod_cast hiZ
      rw [pay1Vec_getD_cast hc hcy hdy i, hmix1, ← mul_assoc, ← mul_assoc] at hiQ
      dsimp only [x, y] at hiQ ⊢
      exact le_of_mul_le_mul_left hiQ hpos1
    have hbr2 : ∀ j : Fin c.cols,
        (∑ i : Fin c.rows, x.getD i.1 0 * c.toMatB i j) ≤
          ∑ i : Fin c.rows, ∑ b : Fin c.cols, x.getD i.1 0 * c.toMatB i b * y.getD b.1 0 := by
      intro j
      have hjZ := (brCheck_iff hlenB).1 hb2 j
      have hjQ : ((vecProdDen dec.2 : ℤ) : ℚ) * ((pay2Vec c dec.1).getD j.1 0 : ℚ) ≤
          ((ListMatrix.dotProduct c.cols (scaleVecNum (vecProdDen dec.2) dec.2)
            (pay2Vec c dec.1) : ℤ) : ℚ) := by exact_mod_cast hjZ
      rw [pay2Vec_getD_cast hc hcx hdx j, hmix2, ← mul_assoc, ← mul_assoc] at hjQ
      dsimp only [x, y] at hjQ ⊢
      exact le_of_mul_le_mul_left hjQ hpos2
    exact ⟨hxlen, hylen, hxnn, hxsum, hynn, hysum, hbr1, hbr2⟩
  · rintro ⟨hew, hcx, hcy, hxlen, hylen, -, hxsum, -, hysum, hbr1, hbr2⟩
    have hdx : dec.1.length = c.rows := by simpa [x] using hxlen
    have hdy : dec.2.length = c.cols := by simpa [y] using hylen
    have hDx : (0 : ℚ) < (vecProdDen dec.1 : ℚ) := by exact_mod_cast vecProdDen_pos hcx
    have hDy : (0 : ℚ) < (vecProdDen dec.2 : ℚ) := by exact_mod_cast vecProdDen_pos hcy
    have hDc : (0 : ℚ) < (clearScale c : ℚ) := by exact_mod_cast clearScale_pos c
    have hsx : (scaleVecNum (vecProdDen dec.1) dec.1).sum = vecProdDen dec.1 :=
      scaleVecNum_sum_eq_vecProdDen_of_sum_eq_one hcx hdx hxsum
    have hsy : (scaleVecNum (vecProdDen dec.2) dec.2).sum = vecProdDen dec.2 :=
      scaleVecNum_sum_eq_vecProdDen_of_sum_eq_one hcy hdy hysum
    have hmix1 := mix1_eq_cast hc hcx hcy hdx hdy
    have hmix2 := mix2_eq_cast hc hcx hcy hdx hdy
    have hb1 : brCheck (vecProdDen dec.1)
        (ListMatrix.dotProduct c.rows (scaleVecNum (vecProdDen dec.1) dec.1) (pay1Vec c dec.2))
        (pay1Vec c dec.2) = true := by
      rw [brCheck_iff hlenA]
      intro i
      have hpos1 : (0 : ℚ) ≤ (vecProdDen dec.1 : ℚ) * (clearScale c : ℚ) * (vecProdDen dec.2 : ℚ) :=
        le_of_lt (mul_pos (mul_pos hDx hDc) hDy)
      have hmul := mul_le_mul_of_nonneg_left (hbr1 i) hpos1
      have hq : ((vecProdDen dec.1 : ℤ) : ℚ) * ((pay1Vec c dec.2).getD i.1 0 : ℚ) ≤
          ((ListMatrix.dotProduct c.rows (scaleVecNum (vecProdDen dec.1) dec.1)
            (pay1Vec c dec.2) : ℤ) : ℚ) := by
        rw [pay1Vec_getD_cast hc hcy hdy i, hmix1, ← mul_assoc]
        simpa only [← mul_assoc] using hmul
      exact_mod_cast hq
    have hb2 : brCheck (vecProdDen dec.2)
        (ListMatrix.dotProduct c.cols (scaleVecNum (vecProdDen dec.2) dec.2) (pay2Vec c dec.1))
        (pay2Vec c dec.1) = true := by
      rw [brCheck_iff hlenB]
      intro j
      have hpos2 : (0 : ℚ) ≤ (vecProdDen dec.2 : ℚ) * (clearScale c : ℚ) * (vecProdDen dec.1 : ℚ) :=
        le_of_lt (mul_pos (mul_pos hDy hDc) hDx)
      have hmul := mul_le_mul_of_nonneg_left (hbr2 j) hpos2
      have hq : ((vecProdDen dec.2 : ℤ) : ℚ) * ((pay2Vec c dec.1).getD j.1 0 : ℚ) ≤
          ((ListMatrix.dotProduct c.cols (scaleVecNum (vecProdDen dec.2) dec.2)
            (pay2Vec c dec.1) : ℤ) : ℚ) := by
        rw [pay2Vec_getD_cast hc hcx hdx j, hmix2, ← mul_assoc]
        simpa only [← mul_assoc] using hmul
      exact_mod_cast hq
    simp only [verifiesDecoded, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hew.symm, hdx⟩, hdy⟩, hcx⟩, hcy⟩, hsx⟩, hsy⟩, hb1⟩, hb2⟩

private lemma verifiesBimatrixNash_eq_true_iff (c : BimatrixCode) (w : List Bool) :
    verifiesBimatrixNash (c, w) = true ↔
      if c.wellFormedB then ∃ s : StrategyPair, w = encWitness s ∧ c.IsRationalNash s.x s.y
      else w = [] := by
  by_cases hwb : c.wellFormedB = true
  · have hc : c.WellFormed := (wellFormed_iff_wellFormedB c).2 hwb
    simp only [verifiesBimatrixNash, hwb, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [verifiesDecoded_iff hc w (witnessDecoder.decode w)]
    constructor
    · rintro ⟨hew, hcx, hcy, hrat⟩
      let x := (witnessDecoder.decode w).1.map mkRatOfPair
      let y := (witnessDecoder.decode w).2.map mkRatOfPair
      refine ⟨⟨x, y⟩, ?_, hrat⟩
      rw [hew, encWitness_eq_pairs x y, map_pair_mkRatOfPair_eq hcx, map_pair_mkRatOfPair_eq hcy]
    · rintro ⟨⟨x, y⟩, rfl, hrat⟩
      let dec0 : List (ℤ × ℕ) × List (ℤ × ℕ) :=
        (x.map (fun q => (q.num, q.den)), y.map (fun q => (q.num, q.den)))
      have hdec0 : witnessDecoder.decode (encWitness ⟨x, y⟩) = dec0 := by
        rw [encWitness_eq_pairs x y, witnessDecoder.decode_enc]
      rw [hdec0]
      have hcx := all_isCanonicalNonnegPair_of_nonneg hrat.2.2.1
      have hcy := all_isCanonicalNonnegPair_of_nonneg hrat.2.2.2.2.1
      rw [map_mkRatOfPair_pair_eq x, map_mkRatOfPair_pair_eq y]
      exact ⟨encWitness_eq_pairs x y, hcx, hcy, hrat⟩
  · have hwf : c.wellFormedB = false := Bool.eq_false_iff.2 hwb
    simp only [verifiesBimatrixNash, hwf, Bool.not_false, ite_true, List.isEmpty_iff,
      Bool.false_eq_true, ite_false]

/-- **Two-player rational Nash equilibrium is in `FNP`.** -/
theorem BimatrixNash_mem_FNP : BimatrixNash ∈ FNP encBimatrix := by
  rw [mem_FNP_iff_exists_bounded]
  refine ⟨witnessPoly, verifiesBimatrixNash, verifiesBimatrixNash_polytime, fun c w => ?_⟩
  rw [verifiesBimatrixNash_eq_true_iff, witnessPoly_eval]
  by_cases hwb : c.wellFormedB = true
  · simp only [BimatrixNash, hwb, ite_true]
  · have hwf : c.wellFormedB = false := Bool.eq_false_iff.2 hwb
    simp only [BimatrixNash, hwf, Bool.false_eq_true, ite_false]
    exact ⟨fun hw => ⟨by subst hw; simp, hw⟩, fun h => h.2⟩

/-! ### Section 4: Positive normalization, vertex encoding, and polytope execution -/

@[instance_reducible]
private def sumLinearOrder (m n : ℕ) : LinearOrder (Fin m ⊕ Fin n) :=
  LinearOrder.lift' finSumFinEquiv finSumFinEquiv.injective

private local instance (priority := high) instLinearOrderFinSumPPAD (m n : ℕ) :
    LinearOrder (Fin m ⊕ Fin n) :=
  sumLinearOrder m n

private local instance (priority := high) instLEFinSumPPAD (m n : ℕ) :
    LE (Fin m ⊕ Fin n) :=
  (sumLinearOrder m n).toLE

private local instance (priority := high) instLTFinSumPPAD (m n : ℕ) :
    LT (Fin m ⊕ Fin n) :=
  (sumLinearOrder m n).toLT

private def finsetOfList (m n : ℕ) (L : List ℕ) : Finset (Fin m ⊕ Fin n) :=
  Finset.univ.filter fun r => (finSumFinEquiv r).1 ∈ L

@[simp]
private lemma mem_finsetOfList {m n : ℕ} {L : List ℕ} {r : Fin m ⊕ Fin n} :
    r ∈ finsetOfList m n L ↔ (finSumFinEquiv r).1 ∈ L := by
  simp [finsetOfList]

private lemma card_finsetOfList {m n : ℕ} {L : List ℕ} (hnd : L.Nodup)
    (hlt : ∀ k ∈ L, k < m + n) : (finsetOfList m n L).card = L.length := by
  have himg : finsetOfList m n L = L.attach.toFinset.image (fun x =>
      finSumFinEquiv.symm ⟨x.1, hlt x.1 x.2⟩) := by
    ext r
    simp only [mem_finsetOfList, Finset.mem_image, List.mem_toFinset, List.mem_attach, true_and]
    constructor
    · intro hr
      refine ⟨⟨(finSumFinEquiv r).1, hr⟩, ?_⟩
      simp
    · rintro ⟨⟨k, hk⟩, hEq⟩
      have h1 := congrArg (fun z => (finSumFinEquiv z).1) hEq
      simp only [Equiv.apply_symm_apply] at h1
      simpa only [← h1] using hk
  rw [himg, Finset.card_image_of_injective]
  · simp [List.toFinset_card_of_nodup (List.nodup_attach.2 hnd)]
  · intro x y hxy
    have h1 := congrArg (fun z => (finSumFinEquiv z).1) hxy
    simp only [Equiv.apply_symm_apply] at h1
    exact Subtype.ext h1

private lemma orderIsoOfFin_finsetOfList {m n k : ℕ} {L : List ℕ} (hsort : L.Pairwise (· < ·))
    (hlt : ∀ r ∈ L, r < m + n) (_hlen : L.length = k)
    (hcard : (finsetOfList m n L).card = k) (i : Fin k) :
    (finSumFinEquiv ((finsetOfList m n L).orderIsoOfFin hcard i).1).1 = L.getD i.1 0 := by
  let T := finsetOfList m n L
  let e : Fin k ≃o T := T.orderIsoOfFin hcard
  let f : Fin k → ℕ := fun j => (finSumFinEquiv ((e j).1)).1
  have hf_mono : StrictMono f := fun a b hab => by
    have hle : f a ≤ f b := (e.le_iff_le.2 hab.le)
    have hne : f a ≠ f b := fun h => hab.ne <| e.injective <| Subtype.ext <|
      finSumFinEquiv.injective <| Fin.ext h
    exact Nat.lt_of_le_of_ne hle hne
  have hsort_ofFn : (List.ofFn f).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp only [List.getElem_ofFn]
    exact hf_mono (Fin.mk_lt_mk.2 hab)
  have hperm : (List.ofFn f).Perm L := by
    refine List.perm_of_nodup_nodup_toFinset_eq hsort_ofFn.nodup hsort.nodup ?_
    ext x
    simp only [List.mem_toFinset, List.mem_ofFn]
    constructor
    · rintro ⟨j, rfl⟩
      exact mem_finsetOfList.1 (e j).2
    · intro hx
      have hmem : finSumFinEquiv.symm ⟨x, hlt x hx⟩ ∈ T := by
        simp [T, mem_finsetOfList, hx]
      refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
      dsimp only [f]
      rw [e.apply_symm_apply]
      simp
  have heq : List.ofFn f = L :=
    hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2)) hsort_ofFn hsort
  have hget := congrArg (fun l => l.getD i.1 0) heq
  rw [← hget, List.getD_ofFn f i 0]

/-- Positive normalized integer matrix `A` of `c`. -/
private def posMatA (c : BimatrixCode) : Matrix (Fin c.rows) (Fin c.cols) ℤ :=
  fun i j => ((posMat c c.matA).getD i.1 []).getD j.1 0

/-- Positive normalized integer matrix `B` of `c`. -/
private def posMatB (c : BimatrixCode) : Matrix (Fin c.rows) (Fin c.cols) ℤ :=
  fun i j => ((posMat c c.matB).getD i.1 []).getD j.1 0

private lemma posMat_getD_eq {c : BimatrixCode} (hc : c.WellFormed)
    (i : Fin c.rows) (j : Fin c.cols) :
    posMatA c i j = scaledEntry (clearScale c) (c.toMatA i j) + shiftVal c ∧
      posMatB c i j = scaledEntry (clearScale c) (c.toMatB i j) + shiftVal c := by
  obtain ⟨_, _, hl2, hr1, hr2⟩ := hc
  have aux : ∀ (M : List (List ℚ)) (hlen : M.length = c.rows)
      (hrows : ∀ r ∈ M, r.length = c.cols),
      ((posMat c M).getD i.1 []).getD j.1 0 =
        scaledEntry (clearScale c) ((M.getD i.1 []).getD j.1 0) + shiftVal c := by
    intro M hlen hrows
    have hi : i.1 < M.length := by rw [hlen]; exact i.2
    have hrlen : (M.getD i.1 []).length = c.cols :=
      hrows _ (List.getD_eq_getElem M [] hi ▸ List.getElem_mem hi)
    have hj : j.1 < (M.getD i.1 []).length := by rw [hrlen]; exact j.2
    have h1 : (posMat c M).getD i.1 [] =
        (M.getD i.1 []).map fun q => scaledEntry (clearScale c) q + shiftVal c :=
      list_getD_map_lt _ M [] [] hi
    rw [h1]
    exact list_getD_map_lt _ (M.getD i.1 []) 0 0 hj
  exact ⟨aux c.matA rfl hr1, aux c.matB hl2 hr2⟩

private lemma abs_scaledEntry_lt_shiftVal {c : BimatrixCode} (hc : c.WellFormed)
    (i : Fin c.rows) (j : Fin c.cols) :
    |scaledEntry (clearScale c) (c.toMatA i j)| < shiftVal c ∧
      |scaledEntry (clearScale c) (c.toMatB i j)| < shiftVal c := by
  obtain ⟨_, _, hl2, hr1, hr2⟩ := hc
  have aux : ∀ (M : List (List ℚ)) (hlen : M.length = c.rows)
      (hrows : ∀ r ∈ M, r.length = c.cols),
      |scaledEntry (clearScale c) ((M.getD i.1 []).getD j.1 0)| ≤
        (M.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum := by
    intro M hlen hrows
    have hi : i.1 < M.length := by rw [hlen]; exact i.2
    have hrmem : M.getD i.1 [] ∈ M := List.getD_eq_getElem M [] hi ▸ List.getElem_mem hi
    have hj : j.1 < (M.getD i.1 []).length := by rw [hrows _ hrmem]; exact j.2
    have hqmem : (M.getD i.1 []).getD j.1 0 ∈ M.getD i.1 [] :=
      List.getD_eq_getElem _ 0 hj ▸ List.getElem_mem hj
    have h1 : |scaledEntry (clearScale c) ((M.getD i.1 []).getD j.1 0)| ≤
        ((M.getD i.1 []).map fun q => |scaledEntry (clearScale c) q|).sum :=
      List.single_le_sum (fun x hx => by
        rcases List.mem_map.1 hx with ⟨q, _, rfl⟩; exact abs_nonneg _)
        _ (List.mem_map.2 ⟨_, hqmem, rfl⟩)
    have h2 : ((M.getD i.1 []).map fun q => |scaledEntry (clearScale c) q|).sum ≤
        (M.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum :=
      List.single_le_sum (fun x hx => by
        rcases List.mem_map.1 hx with ⟨row, _, rfl⟩
        exact List.sum_nonneg fun y hy => by
          rcases List.mem_map.1 hy with ⟨q, _, rfl⟩; exact abs_nonneg _)
        _ (List.mem_map.2 ⟨_, hrmem, rfl⟩)
    exact h1.trans h2
  have hnonneg : ∀ M : List (List ℚ),
      0 ≤ (M.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum := by
    intro M
    exact List.sum_nonneg fun x hx => by
      rcases List.mem_map.1 hx with ⟨row, _, rfl⟩
      exact List.sum_nonneg fun y hy => by
        rcases List.mem_map.1 hy with ⟨q, _, rfl⟩; exact abs_nonneg _
  have hA := aux c.matA rfl hr1
  have hB := aux c.matB hl2 hr2
  have hn1 := hnonneg c.matA
  have hn2 := hnonneg c.matB
  dsimp only [shiftVal, toMatA, toMatB] at *
  exact ⟨by omega, by omega⟩

private lemma shiftVal_pos (c : BimatrixCode) : 1 ≤ shiftVal c := by
  have hnonneg : ∀ M : List (List ℚ),
      0 ≤ (M.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum :=
    fun M => List.sum_nonneg fun x hx => by
      rcases List.mem_map.1 hx with ⟨row, _, rfl⟩
      exact List.sum_nonneg fun y hy => by
        rcases List.mem_map.1 hy with ⟨q, _, rfl⟩; exact abs_nonneg _
  have h1 := hnonneg c.matA
  have h2 := hnonneg c.matB
  dsimp only [shiftVal]
  omega

private lemma posMat_bounds {c : BimatrixCode} (hc : c.WellFormed)
    (i : Fin c.rows) (j : Fin c.cols) :
    1 ≤ HVal c ∧ 1 ≤ posMatA c i j ∧ posMatA c i j ≤ (HVal c : ℤ) ∧
      1 ≤ posMatB c i j ∧ posMatB c i j ≤ (HVal c : ℤ) := by
  have hs := shiftVal_pos c
  have hH : (HVal c : ℤ) = 2 * shiftVal c := by
    dsimp only [HVal]
    push_cast
    rw [abs_of_nonneg (by omega)]
  obtain ⟨hposA, hposB⟩ := posMat_getD_eq hc i j
  obtain ⟨habsA, habsB⟩ := abs_scaledEntry_lt_shiftVal hc i j
  have hA1 : 1 ≤ posMatA c i j := by
    have := neg_abs_le (scaledEntry (clearScale c) (c.toMatA i j))
    omega
  have hA2 : posMatA c i j ≤ (HVal c : ℤ) := by
    have := le_abs_self (scaledEntry (clearScale c) (c.toMatA i j))
    omega
  have hB1 : 1 ≤ posMatB c i j := by
    have := neg_abs_le (scaledEntry (clearScale c) (c.toMatB i j))
    omega
  have hB2 : posMatB c i j ≤ (HVal c : ℤ) := by
    have := le_abs_self (scaledEntry (clearScale c) (c.toMatB i j))
    omega
  exact ⟨by omega, hA1, hA2, hB1, hB2⟩

private lemma isNash_posMat {c : BimatrixCode} (hc : c.WellFormed)
    (x : Fin c.rows → ℝ) (y : Fin c.cols → ℝ) :
    ({ A := (posMatA c).map Int.cast, B := (posMatB c).map Int.cast } :
        BimatrixGame (Fin c.rows) (Fin c.cols)).IsNash x y ↔ c.toGame.IsNash x y := by
  have ⟨_, _, hl2, hr1, hr2⟩ := hc
  have hDc : (0 : ℝ) < (clearScale c : ℝ) := by exact_mod_cast clearScale_pos c
  have hA_eq : ∀ i j, ((posMatA c).map Int.cast) i j =
      (clearScale c : ℝ) * c.toGame.A i j + (shiftVal c : ℝ) := by
    intro i j
    have hi : i.1 < c.matA.length := i.2
    have hrmem := List.getD_eq_getElem c.matA [] hi ▸ List.getElem_mem hi
    have hj : j.1 < (c.matA.getD i.1 []).length := by rw [hr1 _ hrmem]; exact j.2
    have hqmem := List.getD_eq_getElem (c.matA.getD i.1 []) 0 hj ▸ List.getElem_mem hj
    have hdvd := den_dvd_clearScale (Or.inl rfl) hrmem hqmem
    have hsc := congrArg (Rat.cast : ℚ → ℝ) (scaledEntry_cast hdvd)
    push_cast at hsc
    dsimp only [toGame, Matrix.map_apply, toMatA]
    rw [(posMat_getD_eq hc i j).1]
    push_cast
    exact congrArg (· + (shiftVal c : ℝ)) hsc
  have hB_eq : ∀ i j, ((posMatB c).map Int.cast) i j =
      (clearScale c : ℝ) * c.toGame.B i j + (shiftVal c : ℝ) := by
    intro i j
    have hi : i.1 < c.matB.length := by rw [hl2]; exact i.2
    have hrmem := List.getD_eq_getElem c.matB [] hi ▸ List.getElem_mem hi
    have hj : j.1 < (c.matB.getD i.1 []).length := by rw [hr2 _ hrmem]; exact j.2
    have hqmem := List.getD_eq_getElem (c.matB.getD i.1 []) 0 hj ▸ List.getElem_mem hj
    have hdvd := den_dvd_clearScale (Or.inr rfl) hrmem hqmem
    have hsc := congrArg (Rat.cast : ℚ → ℝ) (scaledEntry_cast hdvd)
    push_cast at hsc
    dsimp only [toGame, Matrix.map_apply, toMatB]
    rw [(posMat_getD_eq hc i j).2]
    push_cast
    exact congrArg (· + (shiftVal c : ℝ)) hsc
  let GD : BimatrixGame (Fin c.rows) (Fin c.cols) :=
    BimatrixGame.mk ((clearScale c : ℝ) • c.toGame.A) ((clearScale c : ℝ) • c.toGame.B)
  have hA_eq' : (posMatA c).map (Int.cast : ℤ → ℝ) = (GD.addConst (shiftVal c : ℝ)).A := by
    ext i j
    rw [BimatrixGame.addConst_A_apply]
    exact hA_eq i j
  have hB_eq' : (posMatB c).map (Int.cast : ℤ → ℝ) = (GD.addConst (shiftVal c : ℝ)).B := by
    ext i j
    rw [BimatrixGame.addConst_B_apply]
    exact hB_eq i j
  have hadd : ({ A := (posMatA c).map Int.cast, B := (posMatB c).map Int.cast } :
        BimatrixGame (Fin c.rows) (Fin c.cols)) = GD.addConst (shiftVal c : ℝ) :=
    congr_arg₂ BimatrixGame.mk hA_eq' hB_eq'
  rw [hadd, BimatrixGame.isNash_addConst, BimatrixGame.isNash_smul hDc c.toGame]
private def bitBoundVal (c : BimatrixCode) : ℕ :=
  bitBound c.rows c.cols (HVal c)

/-- Target Shapley orientation `(-1) ^ (c.rows + c.cols)` computed without exponentiation. -/
private def targetSign (c : BimatrixCode) : ℤ :=
  if decide (((c.rows + c.cols : ℤ) - 2 * ((c.rows + c.cols : ℤ).tdiv 2)) = 0) then 1 else -1

private lemma targetSign_eq (c : BimatrixCode) :
    targetSign c = (-1 : ℤ) ^ (c.rows + c.cols) := by
  have hsub : ∀ k : ℕ, (k : ℤ) - 2 * ((k : ℤ).tdiv 2) = ((k % 2 : ℕ) : ℤ) := by
    intro k
    have ht : (k : ℤ).tdiv 2 = ((k / 2 : ℕ) : ℤ) := rfl
    rw [ht]
    have hdiv := Nat.div_add_mod k 2
    omega
  dsimp only [targetSign]
  rw [← Int.natCast_add, hsub]
  rcases Nat.mod_two_eq_zero_or_one (c.rows + c.cols) with h | h
  · simp only [h, Int.natCast_zero, decide_true, ite_true]
    rw [← Nat.div_add_mod (c.rows + c.cols) 2, h, add_zero, pow_mul]
    simp
  · simp only [h, Int.natCast_one, show decide ((1 : ℤ) = 0) = false by decide, Bool.false_eq_true,
      ite_false]
    rw [← Nat.div_add_mod (c.rows + c.cols) 2, h, pow_add, pow_mul]
    simp

/-- Vertex bit-length for the PPAD graph: `2 * (rows + cols)` on well-formed inputs, else `0`. -/
@[expose] def vertexLen (c : BimatrixCode) : ℕ :=
  if c.wellFormedB then 2 * (c.rows + c.cols) else 0

/-- Decode player-1 tight row indices in `[0 .. rows + cols - 1]` from bit string `u`,
XORed with the artificial origin mask `k < rows`. -/
private def decodeT₁ (c : BimatrixCode) (u : List Bool) : List ℕ :=
  (List.range (c.rows + c.cols)).filter fun k => (u.getD k false) != decide (k < c.rows)

/-- Decode player-2 tight row indices in `[0 .. rows + cols - 1]` from bit string `u`,
XORed with the artificial origin mask `rows ≤ k`. -/
private def decodeT₂ (c : BimatrixCode) (u : List Bool) : List ℕ :=
  (List.range (c.rows + c.cols)).filter fun k =>
    (u.getD (c.rows + c.cols + k) false) != decide (c.rows ≤ k)

/-- Encode basis label lists `(T₁, T₂)` into a `2 * (rows + cols)`-bit vertex string, mapping the
artificial origin `([0..m-1], [m..m+n-1])` to `0^(2*(m+n))`. -/
private def encodeNodes (c : BimatrixCode) (T₁ T₂ : List ℕ) : List Bool :=
  let d := c.rows + c.cols
  (List.range (2 * d)).map fun k =>
    if k < d then decide (k ∈ T₁) != decide (k < c.rows)
    else decide (k - d ∈ T₂) != decide (c.rows ≤ k - d)

private lemma length_encodeNodes (c : BimatrixCode) (T₁ T₂ : List ℕ) :
    (encodeNodes c T₁ T₂).length = 2 * (c.rows + c.cols) := by
  simp [encodeNodes]

private lemma encodeNodes_origin (c : BimatrixCode) :
    encodeNodes c (List.range c.rows) ((List.range c.cols).map (· + c.rows)) =
      zeroVertex (2 * (c.rows + c.cols)) := by
  refine List.ext_getElem (by simp [encodeNodes]) fun k hk1 hk2 => ?_
  simp only [encodeNodes, List.length_map, List.length_range] at hk1
  simp only [encodeNodes, zeroVertex, List.getElem_map, List.getElem_range, List.getElem_replicate]
  by_cases hkd : k < c.rows + c.cols
  · rw [ite_eq_left hkd]
    simp [List.mem_range, bne_self_eq_false]
  · rw [ite_eq_right hkd]
    have hmem : (k - (c.rows + c.cols) ∈
        (List.range c.cols).map (· + c.rows)) ↔ c.rows ≤ k - (c.rows + c.cols) := by
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨j, _, hj⟩; omega
      · intro hge
        refine ⟨k - (c.rows + c.cols) - c.rows, by omega, by omega⟩
    simp [hmem, bne_self_eq_false]

private lemma decodeT₁_sorted (c : BimatrixCode) (u : List Bool) :
    (decodeT₁ c u).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private lemma decodeT₂_sorted (c : BimatrixCode) (u : List Bool) :
    (decodeT₂ c u).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private lemma decodeT₁_lt (c : BimatrixCode) (u : List Bool) {k : ℕ} (hk : k ∈ decodeT₁ c u) :
    k < c.rows + c.cols := by
  simp only [decodeT₁, List.mem_filter, List.mem_range] at hk
  exact hk.1

private lemma decodeT₂_lt (c : BimatrixCode) (u : List Bool) {k : ℕ} (hk : k ∈ decodeT₂ c u) :
    k < c.rows + c.cols := by
  simp only [decodeT₂, List.mem_filter, List.mem_range] at hk
  exact hk.1

private lemma encodeNodes_decode {c : BimatrixCode} {u : List Bool}
    (hu : u.length = 2 * (c.rows + c.cols)) :
    encodeNodes c (decodeT₁ c u) (decodeT₂ c u) = u := by
  refine List.ext_getElem (by simp [encodeNodes, hu]) fun k hk1 hk2 => ?_
  simp only [encodeNodes, List.getElem_map, List.getElem_range]
  have hget : u.getD k false = u[k] := List.getD_eq_getElem u false hk2
  by_cases hkd : k < c.rows + c.cols
  · rw [ite_eq_left hkd]
    have hkmem : decide (k ∈ decodeT₁ c u) = (u[k] != decide (k < c.rows)) := by
      simp only [decodeT₁, List.mem_filter, List.mem_range, hkd, true_and, hget]
      cases u[k] <;> cases decide (k < c.rows) <;> decide
    rw [hkmem]
    cases u[k] <;> cases decide (k < c.rows) <;> rfl
  · rw [ite_eq_right hkd]
    have hkd2 : k - (c.rows + c.cols) < c.rows + c.cols := by
      simp only [encodeNodes, List.length_map, List.length_range] at hk1
      omega
    have hkmem : decide (k - (c.rows + c.cols) ∈ decodeT₂ c u) =
        (u[k] != decide (c.rows ≤ k - (c.rows + c.cols))) := by
      have hsumk : c.rows + c.cols + (k - (c.rows + c.cols)) = k := by omega
      simp only [decodeT₂, List.mem_filter, List.mem_range, hkd2, true_and, hsumk, hget]
      cases u[k] <;> cases decide (c.rows ≤ k - (c.rows + c.cols)) <;> decide
    rw [hkmem]
    cases u[k] <;> cases decide (c.rows ≤ k - (c.rows + c.cols)) <;> rfl

private lemma decodeT₁_encodeNodes {c : BimatrixCode} (T₁ T₂ : List ℕ) {k : ℕ}
    (hk : k < c.rows + c.cols) :
    k ∈ decodeT₁ c (encodeNodes c T₁ T₂) ↔ k ∈ T₁ := by
  have hklen : k < (encodeNodes c T₁ T₂).length := by simp [encodeNodes]; omega
  simp only [decodeT₁, List.mem_filter, List.mem_range, hk, true_and]
  rw [List.getD_eq_getElem _ false hklen]
  simp only [encodeNodes, List.getElem_map, List.getElem_range, ite_eq_left hk]
  cases hkT : decide (k ∈ T₁) <;> cases decide (k < c.rows) <;> simp_all

private lemma decodeT₂_encodeNodes {c : BimatrixCode} (T₁ T₂ : List ℕ) {k : ℕ}
    (hk : k < c.rows + c.cols) :
    k ∈ decodeT₂ c (encodeNodes c T₁ T₂) ↔ k ∈ T₂ := by
  have hklen : c.rows + c.cols + k < (encodeNodes c T₁ T₂).length := by
    simp [encodeNodes]; omega
  simp only [decodeT₂, List.mem_filter, List.mem_range, hk, true_and]
  rw [List.getD_eq_getElem _ false hklen]
  have hnotlt : ¬ c.rows + c.cols + k < c.rows + c.cols := by omega
  simp only [encodeNodes, List.getElem_map, List.getElem_range, ite_eq_right hnotlt,
    Nat.add_sub_cancel_left]
  cases hkT : decide (k ∈ T₂) <;> cases decide (c.rows ≤ k) <;> simp_all

private lemma decodeT₁_zeroVertex (c : BimatrixCode) :
    decodeT₁ c (zeroVertex (2 * (c.rows + c.cols))) = List.range c.rows := by
  have hperm : (decodeT₁ c (zeroVertex (2 * (c.rows + c.cols)))).Perm (List.range c.rows) := by
    refine List.perm_of_nodup_nodup_toFinset_eq (decodeT₁_sorted c _).nodup List.nodup_range ?_
    ext k
    simp only [List.mem_toFinset, List.mem_range, decodeT₁, List.mem_filter, zeroVertex]
    constructor
    · rintro ⟨hk, hne⟩
      rw [List.getD_replicate false (by omega)] at hne
      simpa using hne
    · intro hk
      have hk2 : k < c.rows + c.cols := by omega
      simp [hk2, hk]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2))
    (decodeT₁_sorted c _) List.pairwise_lt_range

private lemma decodeT₂_zeroVertex (c : BimatrixCode) :
    decodeT₂ c (zeroVertex (2 * (c.rows + c.cols))) = (List.range c.cols).map (· + c.rows) := by
  have hsort : ((List.range c.cols).map (· + c.rows)).Pairwise (· < ·) :=
    List.pairwise_lt_range.map _ fun _ _ h => by omega
  have hperm : (decodeT₂ c (zeroVertex (2 * (c.rows + c.cols)))).Perm
      ((List.range c.cols).map (· + c.rows)) := by
    refine List.perm_of_nodup_nodup_toFinset_eq (decodeT₂_sorted c _).nodup hsort.nodup ?_
    ext k
    simp only [List.mem_toFinset, List.mem_map, List.mem_range, decodeT₂, List.mem_filter,
      zeroVertex]
    constructor
    · rintro ⟨hk, hne⟩
      rw [List.getD_replicate false (by omega)] at hne
      have hkge : c.rows ≤ k := by simpa using hne
      exact ⟨k - c.rows, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      have hk2 : j + c.rows < c.rows + c.cols := by omega
      simp [hk2]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2))
    (decodeT₂_sorted c _) hsort

private theorem mapToBitsWithInput_poly {α β : Type} {encIn : α ↪ List Bool}
    {enc : β ↪ List Bool} {list : α → List β} {f : α → β → Bool}
    (hlist : ComputableInPolyTime list encIn (encList enc))
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair encIn enc) encBool) :
    ComputableInPolyTime (fun a => (list a).map (f a)) encIn encBits :=
  .of_tidy (ComputableTidilyInPolyTime.mapToBitsWithInput hlist.tidy hf.tidy)

private theorem bool_xor_polytime {α : Type} {encIn : α ↪ List Bool}
    {a b : α → Bool} (ha : ComputableInPolyTime a encIn encBool)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => a x != b x) encIn encBool := by
  have h1 : ComputableInPolyTime (fun p : Bool × Bool => p.1 != p.2)
      (encPair encBool encBool) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.of_finite _)
  exact h1.comp (ha.prod hb)

@[local fun_prop]
private theorem bitBoundVal_polytime :
    ComputableInPolyTime bitBoundVal encBimatrix encUnary := by
  have hlog : ∀ H : ℕ, Nat.log 2 H = H.size - 1 := fun H => by
    rw [← Nat.log2_eq_log_two, Nat.log2_eq_size_sub_one]
  have hb : ComputableInPolyTime
      (fun c : BimatrixCode => 4 * (c.rows + c.cols) * (c.rows + c.cols + ((HVal c).size - 1) + 3))
      encBimatrix encUnary := by
    have hd := unary_add.comp (codeRows_polytime.prod codeCols_polytime)
    have h4d := unary_mul.comp ((const 4).prod hd)
    have hsize := unary_sub.comp ((binary_size.comp HVal_polytime).prod (const 1))
    have hsum := unary_add.comp ((unary_add.comp (hd.prod hsize)).prod (const 3))
    exact unary_mul.comp (h4d.prod hsum)
  exact hb.of_enc_eq (encD := encUnary) fun c => by
    dsimp only [bitBoundVal, bitBound]
    rw [hlog]

@[local fun_prop]
private theorem targetSign_polytime :
    ComputableInPolyTime targetSign encBimatrix encIntBin := by
  unfold targetSign
  have hd : ComputableInPolyTime (fun c : BimatrixCode => (c.rows + c.cols : ℤ))
      encBimatrix encIntBin :=
    intBin_natCast.comp (unary_to_binary.comp
      (unary_add.comp (codeRows_polytime.prod codeCols_polytime)))
  have hrem := intBin_sub' hd (intBin_mul' (const 2) (intBin_tdiv' hd (const 2)))
  exact ite' (decide_eq' hrem (const (encOut := encIntBin) 0))
    (const (encOut := encIntBin) 1) (const (encOut := encIntBin) (-1))

@[local fun_prop]
private theorem vertexLen_polytime :
    ComputableInPolyTime vertexLen encBimatrix encUnary := by
  unfold vertexLen
  exact ite' wellFormedB_polytime
    (unary_mul.comp ((const 2).prod (unary_add.comp (codeRows_polytime.prod codeCols_polytime))))
    (const 0)

@[local fun_prop]
private theorem decodeT₁_polytime :
    ComputableInPolyTime (fun p : BimatrixCode × List Bool => decodeT₁ p.1 p.2)
      (encPair encBimatrix encBits) (encList encUnary) := by
  unfold decodeT₁
  have hc0 := fst encBimatrix encBits
  have hu0 := snd encBimatrix encBits
  refine filterWithInput
    (range.comp (unary_add.comp ((codeRows_polytime.comp hc0).prod
      (codeCols_polytime.comp hc0)))) ?_
  have hc := hc0.comp (fst (encPair encBimatrix encBits) encUnary)
  have hu := hu0.comp (fst (encPair encBimatrix encBits) encUnary)
  have hk := snd (encPair encBimatrix encBits) encUnary
  exact bool_xor_polytime
    (bitsGetD false |>.comp (hu.prod hk))
    (unary_lt' hk (codeRows_polytime.comp hc))

@[local fun_prop]
private theorem decodeT₂_polytime :
    ComputableInPolyTime (fun p : BimatrixCode × List Bool => decodeT₂ p.1 p.2)
      (encPair encBimatrix encBits) (encList encUnary) := by
  unfold decodeT₂
  have hc0 := fst encBimatrix encBits
  have hu0 := snd encBimatrix encBits
  have hd0 := unary_add.comp ((codeRows_polytime.comp hc0).prod (codeCols_polytime.comp hc0))
  refine filterWithInput (range.comp hd0) ?_
  have hc := hc0.comp (fst (encPair encBimatrix encBits) encUnary)
  have hu := hu0.comp (fst (encPair encBimatrix encBits) encUnary)
  have hd := hd0.comp (fst (encPair encBimatrix encBits) encUnary)
  have hk := snd (encPair encBimatrix encBits) encUnary
  exact bool_xor_polytime
    (bitsGetD false |>.comp (hu.prod (unary_add.comp (hd.prod hk))))
    (unary_le' (codeRows_polytime.comp hc) hk)

private theorem encodeNodes_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {T₁ T₂ : α → List ℕ}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (h1 : ComputableInPolyTime T₁ encIn (encList encUnary))
    (h2 : ComputableInPolyTime T₂ encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => encodeNodes (c x) (T₁ x) (T₂ x)) encIn encBits := by
  unfold encodeNodes
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hd := unary_add.comp (hm.prod hn)
  refine mapToBitsWithInput_poly (range.comp (unary_mul.comp ((const 2).prod hd))) ?_
  have hlt := unary_lt' (snd encIn encUnary) (hd.comp (fst encIn encUnary))
  have hsub := unary_sub.comp ((snd encIn encUnary).prod (hd.comp (fst encIn encUnary)))
  have hle := unary_le' (hm.comp (fst encIn encUnary)) hsub
  have hk1 := bool_xor_polytime (decide_mem (h1.comp (fst encIn encUnary)) (snd encIn encUnary))
    (unary_lt' (snd encIn encUnary) (hm.comp (fst encIn encUnary)))
  have hk2 := bool_xor_polytime (decide_mem (h2.comp (fst encIn encUnary)) hsub) hle
  exact ite_decide hlt hk1 hk2

/-- All `m + n` rows of `intMatP (posMatB c)` as `List (List ℤ)`. -/
private def allRowsP (c : BimatrixCode) : List (List ℤ) :=
  let Bpos := posMat c c.matB
  tabulateTable (c.rows + c.cols) c.rows fun r i =>
    if r < c.rows then if i = r then -1 else 0 else rowEntry Bpos i (r - c.rows)

/-- All `m + n` entries of the perturbed RHS `pertRhsPInt` for `P_ε`. -/
private def allRhsP (c : BimatrixCode) : List ℤ :=
  let E := bitBoundVal c
  (List.range (c.rows + c.cols)).map fun r =>
    if r < c.rows then 0
    else ((2 ^ (E * c.cols) : ℕ) : ℤ) + ((2 ^ (E * (c.cols - 1 - (r - c.rows))) : ℕ) : ℤ)

/-- All `m + n` rows of `intMatQ (posMatA c)` as `List (List ℤ)`. -/
private def allRowsQ (c : BimatrixCode) : List (List ℤ) :=
  let Apos := posMat c c.matA
  tabulateTable (c.rows + c.cols) c.cols fun r j =>
    if r < c.rows then rowEntry Apos r j else if j = r - c.rows then -1 else 0

/-- All `m + n` entries of the perturbed RHS `pertRhsQInt` for `Q_ε`. -/
private def allRhsQ (c : BimatrixCode) : List ℤ :=
  let E := bitBoundVal c
  (List.range (c.rows + c.cols)).map fun r =>
    if r < c.rows then
      ((2 ^ (E * c.rows) : ℕ) : ℤ) + ((2 ^ (E * (c.rows - 1 - r)) : ℕ) : ℤ)
    else 0

/-- All `m + n` entries of the unperturbed RHS `intRhsP`. -/
private def allIntRhsP (c : BimatrixCode) : List ℤ :=
  (List.range (c.rows + c.cols)).map fun r => if r < c.rows then 0 else 1

/-- All `m + n` entries of the unperturbed RHS `intRhsQ`. -/
private def allIntRhsQ (c : BimatrixCode) : List ℤ :=
  (List.range (c.rows + c.cols)).map fun r => if r < c.rows then 1 else 0

/-- Extract the `k × k` basis submatrix for row list `T` from full row table `allRows`. -/
private def subRows (k : ℕ) (allRows : List (List ℤ)) (T : List ℕ) : List (List ℤ) :=
  T.map fun r => (List.range k).map fun j => rowEntry allRows r j

/-- Extract the `k`-element RHS vector for row list `T` from full RHS list `rhsAll`. -/
private def subRhs (rhsAll : List ℤ) (T : List ℕ) : List ℤ :=
  T.map fun r => rowEntry [rhsAll] 0 r

/-- Replace column `col` of `k × k` list matrix `M` with vector `rhs`. -/
private def updateColRows (k : ℕ) (M : List (List ℤ)) (col : ℕ) (rhs : List ℤ) :
    List (List ℤ) :=
  tabulateTable k k fun r j => if j = col then rowEntry [rhs] 0 r else rowEntry M r j

/-- Cramer vector `(det (M.updateCol i rhs))_{i < k}`. -/
private def cramerVecRows (k : ℕ) (M : List (List ℤ)) (rhs : List ℤ) : List ℤ :=
  (List.range k).map fun i => detRows (updateColRows k M i rhs)

/-- Executable feasibility check matching `IsFeasibleBasis` on `(k, allRows, rhsAll, T)`. -/
private def isFeasibleBasisRows (k d : ℕ) (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (T : List ℕ) : Bool :=
  let M := subRows k allRows T
  let D := detRows M
  let cv := cramerVecRows k M (subRhs rhsAll T)
  decide (D ≠ 0) &&
    (List.range d).all fun r =>
      let row := (List.range k).map fun j => rowEntry allRows r j
      decide (D.sign * ListMatrix.dotProduct k row cv ≤ |D| * rowEntry [rhsAll] 0 r)

private lemma rowCellC_polytime :
    ComputableInPolyTime (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ => p.1.1.1)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encBimatrix :=
  (fst encBimatrix encIntTable).comp
    ((fst (encPair encBimatrix encIntTable) encUnary).comp
      (fst (encPair (encPair encBimatrix encIntTable) encUnary) encUnary))

private lemma rowCellM_polytime :
    ComputableInPolyTime (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ => p.1.1.2)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encIntTable :=
  (snd encBimatrix encIntTable).comp
    ((fst (encPair encBimatrix encIntTable) encUnary).comp
      (fst (encPair (encPair encBimatrix encIntTable) encUnary) encUnary))

private lemma rowCellR_polytime :
    ComputableInPolyTime (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ => p.1.2)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encUnary :=
  (snd (encPair encBimatrix encIntTable) encUnary).comp
    (fst (encPair (encPair encBimatrix encIntTable) encUnary) encUnary)

private lemma rowCellK_polytime :
    ComputableInPolyTime (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ => p.2)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encUnary :=
  snd (encPair (encPair encBimatrix encIntTable) encUnary) encUnary

private lemma tabulateSplitRows_polytime {dim : BimatrixCode → ℕ}
    (hdim : ComputableInPolyTime dim encBimatrix encUnary)
    {mat : BimatrixCode → List (List ℤ)}
    (hmat : ComputableInPolyTime mat encBimatrix encIntTable)
    {entry : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ → ℤ}
    (hentry : ComputableInPolyTime entry
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encIntBin)
    {g : BimatrixCode → List (List ℤ)}
    (hg : ∀ c, g c = tabulateTable (c.rows + c.cols) (dim c) fun r k =>
      entry (((c, mat c), r), k)) :
    ComputableInPolyTime g encBimatrix encIntTable := by
  have hwith : ComputableInPolyTime
      (fun p : BimatrixCode × List (List ℤ) =>
        tabulateTable (p.1.rows + p.1.cols) (dim p.1) fun r k => entry ((p, r), k))
      (encPair encBimatrix encIntTable) encIntTable :=
    computableInPolyTime_tabulateTable
      (unary_add.comp ((codeRows_polytime.comp (fst encBimatrix encIntTable)).prod
        (codeCols_polytime.comp (fst encBimatrix encIntTable))))
      (hdim.comp (fst encBimatrix encIntTable)) hentry
  exact (hwith.comp ((id' (encIn := encBimatrix)).prod hmat)).of_enc_eq
    (encD := encIntTable) fun c => congrArg encIntTable (hg c)

@[local fun_prop]
private theorem allRowsP_polytime :
    ComputableInPolyTime allRowsP encBimatrix encIntTable := by
  have hentry : ComputableInPolyTime
      (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ =>
        if p.1.2 < p.1.1.1.rows then if p.2 = p.1.2 then -1 else 0
        else rowEntry p.1.1.2 p.2 (p.1.2 - p.1.1.1.rows))
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encIntBin := by
    have hm := codeRows_polytime.comp rowCellC_polytime
    have h1 := ite_decide (decide_eq' rowCellK_polytime rowCellR_polytime)
      (const (encOut := encIntBin) (-1)) (const (encOut := encIntBin) 0)
    have h2 := computableInPolyTime_rowEntry rowCellM_polytime rowCellK_polytime
      (unary_sub.comp (rowCellR_polytime.prod hm))
    exact ite_decide (unary_lt' rowCellR_polytime hm) h1 h2
  exact tabulateSplitRows_polytime codeRows_polytime posMatB_polytime hentry fun _ => rfl

@[local fun_prop]
private theorem allRowsQ_polytime :
    ComputableInPolyTime allRowsQ encBimatrix encIntTable := by
  have hentry : ComputableInPolyTime
      (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ =>
        if p.1.2 < p.1.1.1.rows then rowEntry p.1.1.2 p.1.2 p.2
        else if p.2 = p.1.2 - p.1.1.1.rows then -1 else 0)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encIntBin := by
    have hm := codeRows_polytime.comp rowCellC_polytime
    have h1 := computableInPolyTime_rowEntry rowCellM_polytime rowCellR_polytime rowCellK_polytime
    have h2 := ite_decide
      (decide_eq' rowCellK_polytime (unary_sub.comp (rowCellR_polytime.prod hm)))
      (const (encOut := encIntBin) (-1)) (const (encOut := encIntBin) 0)
    exact ite_decide (unary_lt' rowCellR_polytime hm) h1 h2
  exact tabulateSplitRows_polytime codeCols_polytime posMatA_polytime hentry fun _ => rfl

@[local fun_prop]
private theorem allRhsP_polytime :
    ComputableInPolyTime allRhsP encBimatrix (encList encIntBin) := by
  unfold allRhsP
  refine mapWithInput (encA := encUnary)
    (range.comp (unary_add.comp (codeRows_polytime.prod codeCols_polytime))) ?_
  have hc := fst encBimatrix encUnary
  have hr := snd encBimatrix encUnary
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hE := bitBoundVal_polytime.comp hc
  have hp1 := intBin_natCast.comp (binary_two_pow.comp (unary_mul.comp (hE.prod hn)))
  have hexp2 := unary_sub.comp ((unary_sub.comp (hn.prod (const 1))).prod
    (unary_sub.comp (hr.prod hm)))
  have hp2 := intBin_natCast.comp (binary_two_pow.comp (unary_mul.comp (hE.prod hexp2)))
  exact ite_decide (unary_lt' hr hm) (const 0) (intBin_add' hp1 hp2)

@[local fun_prop]
private theorem allRhsQ_polytime :
    ComputableInPolyTime allRhsQ encBimatrix (encList encIntBin) := by
  unfold allRhsQ
  refine mapWithInput (encA := encUnary)
    (range.comp (unary_add.comp (codeRows_polytime.prod codeCols_polytime))) ?_
  have hc := fst encBimatrix encUnary
  have hr := snd encBimatrix encUnary
  have hm := codeRows_polytime.comp hc
  have hE := bitBoundVal_polytime.comp hc
  have hp1 := intBin_natCast.comp (binary_two_pow.comp (unary_mul.comp (hE.prod hm)))
  have hexp2 := unary_sub.comp ((unary_sub.comp (hm.prod (const 1))).prod hr)
  have hp2 := intBin_natCast.comp (binary_two_pow.comp (unary_mul.comp (hE.prod hexp2)))
  exact ite_decide (unary_lt' hr hm) (intBin_add' hp1 hp2) (const 0)

@[local fun_prop]
private theorem allIntRhsP_polytime :
    ComputableInPolyTime allIntRhsP encBimatrix (encList encIntBin) := by
  unfold allIntRhsP
  refine mapWithInput (encA := encUnary)
    (range.comp (unary_add.comp (codeRows_polytime.prod codeCols_polytime))) ?_
  exact ite_decide (unary_lt' (snd _ _) (codeRows_polytime.comp (fst _ _))) (const 0) (const 1)

@[local fun_prop]
private theorem allIntRhsQ_polytime :
    ComputableInPolyTime allIntRhsQ encBimatrix (encList encIntBin) := by
  unfold allIntRhsQ
  refine mapWithInput (encA := encUnary)
    (range.comp (unary_add.comp (codeRows_polytime.prod codeCols_polytime))) ?_
  exact ite_decide (unary_lt' (snd _ _) (codeRows_polytime.comp (fst _ _))) (const 1) (const 0)

private lemma rowEntry_single (l : List ℤ) (r : ℕ) :
    rowEntry [l] 0 r = l.getD r 0 := by
  simp [rowEntry]

private theorem subRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k : α → ℕ} {allRows : α → List (List ℤ)} {T : α → List ℕ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hall : ComputableInPolyTime allRows encIn encIntTable)
    (hT : ComputableInPolyTime T encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => subRows (k x) (allRows x) (T x)) encIn encIntTable := by
  unfold subRows
  refine mapWithInput (encA := encUnary) hT ?_
  refine mapWithInput (encA := encUnary) (range.comp (hk.comp (fst _ _))) ?_
  exact computableInPolyTime_rowEntry (hall.comp ((fst _ _).comp (fst _ _)))
    ((snd _ _).comp (fst _ _)) (snd _ _)

private theorem subRhs_polytime {α : Type} {encIn : α ↪ List Bool}
    {rhsAll : α → List ℤ} {T : α → List ℕ}
    (hrhs : ComputableInPolyTime rhsAll encIn (encList encIntBin))
    (hT : ComputableInPolyTime T encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => subRhs (rhsAll x) (T x)) encIn (encList encIntBin) := by
  unfold subRhs
  refine mapWithInput (encA := encUnary) hT ?_
  have htbl : ComputableInPolyTime (fun p : α × ℕ => [rhsAll p.1])
      (encPair encIn encUnary) encIntTable := by
    have hcons : ComputableInPolyTime (fun l : List ℤ => [l])
        (encList encIntBin) encIntTable := by
      fun_prop
    exact hcons.comp (hrhs.comp (fst _ _))
  exact computableInPolyTime_rowEntry htbl (const 0) (snd _ _)

private theorem updateColRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k col : α → ℕ} {M : α → List (List ℤ)} {rhs : α → List ℤ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hM : ComputableInPolyTime M encIn encIntTable)
    (hcol : ComputableInPolyTime col encIn encUnary)
    (hrhs : ComputableInPolyTime rhs encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => updateColRows (k x) (M x) (col x) (rhs x))
      encIn encIntTable := by
  unfold updateColRows
  refine computableInPolyTime_tabulateTable hk hk ?_
  have hx := (fst encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)
  have hr := (snd encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)
  have hj := snd (encPair encIn encUnary) encUnary
  have htbl : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => [rhs p.1.1])
      (encPair (encPair encIn encUnary) encUnary) encIntTable := by
    have hcons : ComputableInPolyTime (fun l : List ℤ => [l])
        (encList encIntBin) encIntTable := by
      fun_prop
    exact hcons.comp (hrhs.comp hx)
  exact ite_decide (decide_eq' hj (hcol.comp hx))
    (computableInPolyTime_rowEntry htbl (const 0) hr)
    (computableInPolyTime_rowEntry (hM.comp hx) hr hj)

private theorem cramerVecRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k : α → ℕ} {M : α → List (List ℤ)} {rhs : α → List ℤ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hM : ComputableInPolyTime M encIn encIntTable)
    (hrhs : ComputableInPolyTime rhs encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => cramerVecRows (k x) (M x) (rhs x))
      encIn (encList encIntBin) := by
  unfold cramerVecRows
  refine mapWithInput (encA := encUnary) (range.comp hk) ?_
  exact detRows_polytime.comp (updateColRows_polytime (hk.comp (fst _ _)) (hM.comp (fst _ _))
    (snd _ _) (hrhs.comp (fst _ _)))

private theorem isFeasibleBasisRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k d : α → ℕ} {allRows : α → List (List ℤ)} {rhsAll : α → List ℤ} {T : α → List ℕ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hall : ComputableInPolyTime allRows encIn encIntTable)
    (hrhs : ComputableInPolyTime rhsAll encIn (encList encIntBin))
    (hT : ComputableInPolyTime T encIn (encList encUnary)) :
    ComputableInPolyTime
      (fun x => isFeasibleBasisRows (k x) (d x) (allRows x) (rhsAll x) (T x)) encIn encBool := by
  let encP := encPair encUnary (encPair encUnary (encPair encIntTable
    (encPair (encList encIntBin) (encList encUnary))))
  let baseFn : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ → Bool :=
    fun q => isFeasibleBasisRows q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  have hbase : ComputableInPolyTime baseFn encP encBool := by
    have hq_k : ComputableInPolyTime (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.1)
        encP encUnary := fst _ _
    have hq_d : ComputableInPolyTime (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.2.1)
        encP encUnary := (fst _ _).comp (snd _ _)
    have hq_all : ComputableInPolyTime
        (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.2.2.1) encP encIntTable :=
      (fst _ _).comp ((snd _ _).comp (snd _ _))
    have hq_rhs : ComputableInPolyTime
        (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.2.2.2.1)
        encP (encList encIntBin) :=
      (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
    have hq_T : ComputableInPolyTime
        (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.2.2.2.2)
        encP (encList encUnary) :=
      (snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
    have hM := subRows_polytime hq_k hq_all hq_T
    have hD := detRows_polytime.comp hM
    have hcv := cramerVecRows_polytime hq_k hM (subRhs_polytime hq_rhs hq_T)
    have hallcheck : ComputableInPolyTime
        (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ =>
          (List.range q.2.1).all fun r =>
            decide ((detRows (subRows q.1 q.2.2.1 q.2.2.2.2)).sign *
              ListMatrix.dotProduct q.1 ((List.range q.1).map fun j => rowEntry q.2.2.1 r j)
                (cramerVecRows q.1 (subRows q.1 q.2.2.1 q.2.2.2.2)
                  (subRhs q.2.2.2.1 q.2.2.2.2)) ≤
              |detRows (subRows q.1 q.2.2.1 q.2.2.2.2)| *
                rowEntry [q.2.2.2.1] 0 r)) encP encBool := by
      refine allWithInput (encA := encUnary) (range.comp hq_d) ?_
      have hx := fst encP encUnary
      have hr := snd encP encUnary
      have habs : ComputableInPolyTime
          (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ =>
            |detRows (subRows q.1 q.2.2.1 q.2.2.2.2)|) encP encIntBin :=
        (intBin_natCast.comp (intBin_natAbs.comp hD)).of_enc_eq (encD := encIntBin) fun q => by
          simp only [Function.comp_apply, Int.natCast_natAbs]
      have hrow_r : ComputableInPolyTime
          (fun p : (ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ) × ℕ =>
            (List.range p.1.1).map fun j => rowEntry p.1.2.2.1 p.2 j)
          (encPair encP encUnary) (encList encIntBin) := by
        refine mapWithInput (encA := encUnary) (range.comp (hq_k.comp hx)) ?_
        exact computableInPolyTime_rowEntry
          (hq_all.comp (hx.comp (fst (encPair encP encUnary) encUnary)))
          (hr.comp (fst (encPair encP encUnary) encUnary)) (snd (encPair encP encUnary) encUnary)
      have htbl_rhs : ComputableInPolyTime
          (fun p : (ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ) × ℕ => [p.1.2.2.2.1])
          (encPair encP encUnary) encIntTable := by
        have hcons : ComputableInPolyTime (fun l : List ℤ => [l])
            (encList encIntBin) encIntTable := by
          fun_prop
        exact hcons.comp (hq_rhs.comp hx)
      have hdot := listDotProduct.comp ((hq_k.comp hx).prod (hrow_r.prod (hcv.comp hx)))
      have hlhs := intBin_mul' (intBin_sign.comp (hD.comp hx)) hdot
      have hrhs' := intBin_mul' (habs.comp hx)
        (computableInPolyTime_rowEntry htbl_rhs (const 0) hr)
      exact intBin_le' hlhs hrhs'
    exact bool_and' (bool_not.comp (decide_eq' hD (const 0))) hallcheck
  exact (hbase.comp (hk.prod (hd.prod (hall.prod (hrhs.prod hT))))).of_enc_eq
    (encD := encBool) fun _ => rfl

private lemma subRows_eq_basisMat {m n k : ℕ} (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ)
    (allRows : List (List ℤ))
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) :
    let Tset := finsetOfList m n T
    have hcard : Tset.card = k := (card_finsetOfList hsort.nodup hlt).trans hlen
    (subRows k allRows T).length = k ∧
      (∀ i j : Fin k, rowEntry (subRows k allRows T) i.1 j.1 = basisMat M_int Tset hcard i j) ∧
      detRows (subRows k allRows T) = (basisMat M_int Tset hcard).det := by
  intro Tset hcard
  have hsublen : (subRows k allRows T).length = k := by simp [subRows, hlen]
  have hentry : ∀ i j : Fin k,
      rowEntry (subRows k allRows T) i.1 j.1 = basisMat M_int Tset hcard i j := by
    intro i j
    have hi : i.1 < T.length := by rw [hlen]; exact i.2
    have hrow : (subRows k allRows T).getD i.1 [] =
        (List.range k).map fun j' => rowEntry allRows (T.getD i.1 0) j' :=
      list_getD_map_lt _ T 0 [] hi
    have hj : j.1 < k := j.2
    have hent : rowEntry (subRows k allRows T) i.1 j.1 =
        rowEntry allRows (T.getD i.1 0) j.1 := by
      change ((subRows k allRows T).getD i.1 []).getD j.1 0 = rowEntry allRows (T.getD i.1 0) j.1
      rw [hrow, List.getD_map_range _ 0 hj]
    have hord := orderIsoOfFin_finsetOfList hsort hlt hlen hcard i
    have hmem : T.getD i.1 0 ∈ T := List.getD_mem 0 hi
    have hlt_i : T.getD i.1 0 < m + n := hlt _ hmem
    have hhall := hall ⟨T.getD i.1 0, hlt_i⟩ j
    rw [hent, hhall]
    have hsymm : finSumFinEquiv.symm ⟨T.getD i.1 0, hlt_i⟩ =
        ((finsetOfList m n T).orderIsoOfFin hcard i).1 := by
      apply finSumFinEquiv.injective
      ext
      simp only [Equiv.apply_symm_apply]
      exact hord.symm
    rw [hsymm]
    rfl
  exact ⟨hsublen, hentry, detRows_eq_det_of_rowEntry _ hsublen hentry⟩

private lemma cramerVecRows_eq_cramerVec {m n k : ℕ} (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ)
    (b_int : Fin m ⊕ Fin n → ℤ) (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), rhsAll.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) :
    have hcard : (finsetOfList m n T).card = k := (card_finsetOfList hsort.nodup hlt).trans hlen
    let cv := cramerVecRows k (subRows k allRows T) (subRhs rhsAll T)
    cv.length = k ∧
      ∀ i : Fin k, cv.getD i.1 0 = cramerVec M_int b_int (finsetOfList m n T) hcard i := by
  intro hcard cv
  obtain ⟨_, hentry, _⟩ := subRows_eq_basisMat M_int allRows hall hsort hlt hlen
  have hsubRhs : ∀ r : Fin k,
      (subRhs rhsAll T).getD r.1 0 = b_int ↑(((finsetOfList m n T).orderIsoOfFin hcard) r) := by
    intro r
    have hr : r.1 < T.length := by rw [hlen]; exact r.2
    have h1 : (subRhs rhsAll T).getD r.1 0 = rowEntry [rhsAll] 0 (T.getD r.1 0) :=
      list_getD_map_lt _ T 0 0 hr
    rw [h1, rowEntry_single]
    have hlt_r : T.getD r.1 0 < m + n := hlt _ (List.getD_mem 0 hr)
    rw [hrhs ⟨T.getD r.1 0, hlt_r⟩]
    have hord := orderIsoOfFin_finsetOfList hsort hlt hlen hcard r
    have hsymm : finSumFinEquiv.symm ⟨T.getD r.1 0, hlt_r⟩ =
        ((finsetOfList m n T).orderIsoOfFin hcard r).1 := by
      apply finSumFinEquiv.injective
      ext
      simp only [Equiv.apply_symm_apply]
      exact hord.symm
    rw [hsymm]
  have hlen_cv : cv.length = k := by simp [cv, cramerVecRows]
  have hget : ∀ i : Fin k,
      cv.getD i.1 0 = cramerVec M_int b_int (finsetOfList m n T) hcard i := by
    intro i
    have h1 : cv.getD i.1 0 =
        detRows (updateColRows k (subRows k allRows T) i.1 (subRhs rhsAll T)) :=
      List.getD_map_range _ 0 i.2
    let B := basisMat M_int (finsetOfList m n T) hcard
    let v : Fin k → ℤ := fun r => b_int ↑(((finsetOfList m n T).orderIsoOfFin hcard) r)
    have hup_len : (updateColRows k (subRows k allRows T) i.1 (subRhs rhsAll T)).length = k := by
      simp [updateColRows, tabulateTable]
    have hup_entry : ∀ r j : Fin k,
        rowEntry (updateColRows k (subRows k allRows T) i.1 (subRhs rhsAll T)) r.1 j.1 =
          (B.updateCol i v) r j := by
      intro r j
      dsimp only [updateColRows]
      rw [rowEntry_tabulateTable, ite_eq_left ⟨r.2, j.2⟩, rowEntry_single]
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl, Matrix.updateCol_apply, ite_eq_left rfl]
        exact hsubRhs r
      · have hne : j.1 ≠ i.1 := fun h => hji (Fin.ext h)
        rw [ite_eq_right hne, Matrix.updateCol_apply, ite_eq_right hji]
        exact hentry r j
    rw [h1, detRows_eq_det_of_rowEntry _ hup_len hup_entry, ← Matrix.cramer_apply]
    rfl
  exact ⟨hlen_cv, hget⟩

private lemma isFeasibleBasisRows_iff {m n k : ℕ}
    (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ) (b_int : Fin m ⊕ Fin n → ℤ)
    (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), rhsAll.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) :
    have hcard : (finsetOfList m n T).card = k := (card_finsetOfList hsort.nodup hlt).trans hlen
    isFeasibleBasisRows k (m + n) allRows rhsAll T = true ↔
      IsFeasibleBasis M_int b_int (finsetOfList m n T) hcard := by
  intro hcard
  obtain ⟨_, _, hdet⟩ := subRows_eq_basisMat M_int allRows hall hsort hlt hlen
  obtain ⟨_, hcv⟩ := cramerVecRows_eq_cramerVec M_int b_int allRows rhsAll hall hrhs hsort hlt hlen
  have hdot : ∀ r : Fin (m + n),
      ListMatrix.dotProduct k ((List.range k).map fun j => rowEntry allRows r.1 j)
        (cramerVecRows k (subRows k allRows T) (subRhs rhsAll T)) =
        M_int (finSumFinEquiv.symm r) ⬝ᵥ cramerVec M_int b_int (finsetOfList m n T) hcard := by
    intro r
    rw [dotProduct_eq_fin_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [List.getD_map_range _ 0 j.2, hall r j, hcv j]
  simp only [isFeasibleBasisRows, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, hdet, IsFeasibleBasis]
  constructor
  · rintro ⟨hne, hall_le⟩
    refine ⟨hne, fun r => ?_⟩
    let r' := finSumFinEquiv r
    have h1 := hall_le r'.1 r'.2
    have h2 : finSumFinEquiv.symm r' = r := Equiv.symm_apply_apply finSumFinEquiv r
    rw [hdot r', rowEntry_single, hrhs r', h2] at h1
    exact h1
  · rintro ⟨hne, hall_le⟩
    refine ⟨hne, fun r hr => ?_⟩
    have h1 := hall_le (finSumFinEquiv.symm ⟨r, hr⟩)
    rw [rowEntry_single rhsAll r, hrhs ⟨r, hr⟩, hdot ⟨r, hr⟩]
    exact h1

/-! ### Section 5: Executable pivoting, Shapley orientation, and PPAD graph -/

private lemma finSumFinEquiv_symm_of_lt {m n r : ℕ} (hr : r < m) :
    finSumFinEquiv.symm ⟨r, Nat.lt_of_lt_of_le hr (Nat.le_add_right m n)⟩ = Sum.inl ⟨r, hr⟩ := by
  apply finSumFinEquiv.injective
  simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, Fin.castAdd_mk]

private lemma finSumFinEquiv_symm_of_le {m n r : ℕ} (hm : m ≤ r) (hr : r < m + n) :
    finSumFinEquiv.symm ⟨r, hr⟩ = Sum.inr ⟨r - m, by omega⟩ := by
  apply finSumFinEquiv.injective
  simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right, Fin.natAdd_mk]
  ext
  simp only
  omega

private lemma allRowsP_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) (j : Fin c.rows) :
    rowEntry (allRowsP c) r.1 j.1 = intMatP (posMatB c) (finSumFinEquiv.symm r) j := by
  dsimp only [allRowsP]
  rw [rowEntry_tabulateTable, ite_eq_left ⟨r.2, j.2⟩]
  by_cases hr : r.1 < c.rows
  · have hr' : (r : Fin (c.rows + c.cols)) = ⟨r.1, by omega⟩ := Fin.ext rfl
    rw [ite_eq_left hr, hr', finSumFinEquiv_symm_of_lt hr, intMatP_inl]
    by_cases hjr : j.1 = r.1
    · have hjeq : (⟨r.1, hr⟩ : Fin c.rows) = j := Fin.ext hjr.symm
      rw [ite_eq_left hjr, ite_eq_left hjeq]
    · have hjne : (⟨r.1, hr⟩ : Fin c.rows) ≠ j := fun h => hjr (congrArg Fin.val h).symm
      rw [ite_eq_right hjr, ite_eq_right hjne]
  · have hm : c.rows ≤ r.1 := Nat.le_of_not_lt hr
    rw [ite_eq_right hr, finSumFinEquiv_symm_of_le hm r.2, intMatP_inr]
    rfl

private lemma allRowsQ_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) (j : Fin c.cols) :
    rowEntry (allRowsQ c) r.1 j.1 = intMatQ (posMatA c) (finSumFinEquiv.symm r) j := by
  dsimp only [allRowsQ]
  rw [rowEntry_tabulateTable, ite_eq_left ⟨r.2, j.2⟩]
  by_cases hr : r.1 < c.rows
  · have hr' : (r : Fin (c.rows + c.cols)) = ⟨r.1, by omega⟩ := Fin.ext rfl
    rw [ite_eq_left hr, hr', finSumFinEquiv_symm_of_lt hr, intMatQ_inl]
    rfl
  · have hm : c.rows ≤ r.1 := Nat.le_of_not_lt hr
    rw [ite_eq_right hr, finSumFinEquiv_symm_of_le hm r.2, intMatQ_inr]
    by_cases hjr : j.1 = r.1 - c.rows
    · have hjeq : (⟨r.1 - c.rows, by omega⟩ : Fin c.cols) = j := Fin.ext hjr.symm
      rw [ite_eq_left hjr, ite_eq_left hjeq]
    · have hjne : (⟨r.1 - c.rows, by omega⟩ : Fin c.cols) ≠ j :=
        fun h => hjr (congrArg Fin.val h).symm
      rw [ite_eq_right hjr, ite_eq_right hjne]

private lemma getD_map_range_sumElim {m n : ℕ} {h : ℕ → ℤ}
    {f' : Fin m → ℤ} {g' : Fin n → ℤ}
    (hf : ∀ i : Fin m, h i.1 = f' i)
    (hg : ∀ j : Fin n, h (m + j.1) = g' j) (r : Fin (m + n)) :
    ((List.range (m + n)).map h).getD r.1 0 = Sum.elim f' g' (finSumFinEquiv.symm r) := by
  rw [List.getD_map_range _ 0 r.2]
  by_cases hr : r.1 < m
  · have hr' : r = ⟨r.1, by omega⟩ := Fin.ext rfl
    rw [hr', finSumFinEquiv_symm_of_lt hr, Sum.elim_inl]
    exact hf ⟨r.1, hr⟩
  · have hm : m ≤ r.1 := Nat.le_of_not_lt hr
    rw [finSumFinEquiv_symm_of_le hm r.2, Sum.elim_inr, ← hg ⟨r.1 - m, by omega⟩]
    exact congrArg h (by dsimp only; omega)

private lemma allRhsP_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) :
    (allRhsP c).getD r.1 0 =
      pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) (finSumFinEquiv.symm r) :=
  getD_map_range_sumElim (fun i => ite_eq_left i.2) (fun _ => by simp [pow_mul]) r

private lemma allRhsQ_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) :
    (allRhsQ c).getD r.1 0 =
      pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) (finSumFinEquiv.symm r) :=
  getD_map_range_sumElim (fun i => by simp [i.2, pow_mul]) (fun _ => by simp) r

private lemma allIntRhsP_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) :
    (allIntRhsP c).getD r.1 0 = intRhsP c.rows c.cols (finSumFinEquiv.symm r) :=
  getD_map_range_sumElim (fun i => ite_eq_left i.2) (fun _ => by simp) r

private lemma allIntRhsQ_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) :
    (allIntRhsQ c).getD r.1 0 = intRhsQ c.rows c.cols (finSumFinEquiv.symm r) :=
  getD_map_range_sumElim (fun i => ite_eq_left i.2) (fun _ => by simp) r

private lemma pertP_nondegenerate {c : BimatrixCode} (hc : c.WellFormed) :
    IsNondegenerateSystem
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) := by
  have hK : (Matrix.kernelVecBound c.rows (HVal c) * (c.cols + 1) : ℤ) <
      (2 : ℤ) ^ bitBoundVal c := by
    exact_mod_cast kernelVecBound_mul_lt_two_pow_bitBound hc.1 hc.2.1
  exact isNondegenerateSystem_pertP (posMat_bounds hc ⟨0, hc.1⟩ ⟨0, hc.2.1⟩).1
    (fun i j => ⟨(posMat_bounds hc i j).2.2.2.1, (posMat_bounds hc i j).2.2.2.2⟩) hK

private lemma pertQ_nondegenerate {c : BimatrixCode} (hc : c.WellFormed) :
    IsNondegenerateSystem
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) := by
  have hK : (Matrix.kernelVecBound c.cols (HVal c) * (c.rows + 1) : ℤ) <
      (2 : ℤ) ^ bitBoundVal c := by
    exact_mod_cast kernelVecBound_mul_lt_two_pow_bitBound_symm hc.1 hc.2.1
  exact isNondegenerateSystem_pertQ (posMat_bounds hc ⟨0, hc.1⟩ ⟨0, hc.2.1⟩).1
    (fun i j => ⟨(posMat_bounds hc i j).2.1, (posMat_bounds hc i j).2.2.1⟩) hK

private lemma pertP_recession {c : BimatrixCode} (hc : c.WellFormed) (v : Fin c.rows → ℚ)
    (hv : ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ) *ᵥ
      v ≤ 0) :
    v = 0 :=
  recession_intMatP hc.2.1 (fun i j => (posMat_bounds hc i j).2.2.2.1) v hv

private lemma pertQ_recession {c : BimatrixCode} (hc : c.WellFormed) (v : Fin c.cols → ℚ)
    (hv : ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ) *ᵥ
      v ≤ 0) :
    v = 0 :=
  recession_intMatQ hc.1 (fun i j => (posMat_bounds hc i j).2.1) v hv

/-- Sorted replacement `(T \ {l}) ∪ {c}` bounded below `d`. -/
private def replaceSorted (d : ℕ) (T : List ℕ) (l c : ℕ) : List ℕ :=
  (List.range d).filter fun x => decide (x = c) || (decide (x ∈ T) && !decide (x = l))

private lemma replaceSorted_sorted (d : ℕ) (T : List ℕ) (l c : ℕ) :
    (replaceSorted d T l c).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private lemma replaceSorted_lt {d : ℕ} {T : List ℕ} {l c x : ℕ}
    (hx : x ∈ replaceSorted d T l c) : x < d := by
  simp only [replaceSorted, List.mem_filter, List.mem_range] at hx
  exact hx.1

private lemma mem_replaceSorted {d : ℕ} {T : List ℕ} {l c x : ℕ} :
    x ∈ replaceSorted d T l c ↔ x < d ∧ (x = c ∨ (x ∈ T ∧ x ≠ l)) := by
  simp only [replaceSorted, List.mem_filter, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]

private lemma finsetOfList_replaceSorted {m n : ℕ} {T : List ℕ}
    {l' c' : Fin m ⊕ Fin n} :
    finsetOfList m n (replaceSorted (m + n) T (finSumFinEquiv l').1 (finSumFinEquiv c').1) =
      insert c' ((finsetOfList m n T).erase l') := by
  ext r
  simp only [mem_finsetOfList, Finset.mem_insert, Finset.mem_erase, mem_replaceSorted,
    (finSumFinEquiv r).2, true_and]
  have heq : ∀ a b : Fin m ⊕ Fin n, (finSumFinEquiv a).1 = (finSumFinEquiv b).1 ↔ a = b :=
    fun a b =>
      ⟨fun h => finSumFinEquiv.injective (Fin.ext h),
        fun h => congrArg (fun z => (finSumFinEquiv z).1) h⟩
  simp only [ne_eq, heq]
  constructor
  · rintro (rfl | ⟨hr, hne⟩)
    · exact .inl rfl
    · exact .inr ⟨hne, hr⟩
  · rintro (rfl | ⟨hne, hr⟩)
    · exact .inl rfl
    · exact .inr ⟨hr, hne⟩

private lemma replaceSorted_polytime {α : Type} {encIn : α ↪ List Bool}
    {d : α → ℕ} {T : α → List ℕ} {l c : α → ℕ}
    (hd : ComputableInPolyTime d encIn encUnary)
    (hT : ComputableInPolyTime T encIn (encList encUnary))
    (hl : ComputableInPolyTime l encIn encUnary)
    (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => replaceSorted (d x) (T x) (l x) (c x))
      encIn (encList encUnary) := by
  unfold replaceSorted
  refine filterWithInput (range.comp hd) ?_
  have hx := fst encIn encUnary
  have he := snd encIn encUnary
  exact bool_or' (decide_eq' he (hc.comp hx))
    (bool_and' (decide_mem (hT.comp hx) he) (bool_not.comp (decide_eq' he (hl.comp hx))))

/-- Executable pivot step on a sorted basis list `T` dropping label `l`. -/
private def pivotBasisRows (k d : ℕ) (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (T : List ℕ) (l : ℕ) : List ℕ :=
  ((List.range d).find? fun c =>
    !decide (c ∈ T) && isFeasibleBasisRows k d allRows rhsAll (replaceSorted d T l c)).elim T
    (replaceSorted d T l)

private theorem pivotBasisRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k d : α → ℕ} {allRows : α → List (List ℤ)} {rhsAll : α → List ℤ}
    {T : α → List ℕ} {l : α → ℕ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hall : ComputableInPolyTime allRows encIn encIntTable)
    (hrhs : ComputableInPolyTime rhsAll encIn (encList encIntBin))
    (hT : ComputableInPolyTime T encIn (encList encUnary))
    (hl : ComputableInPolyTime l encIn encUnary) :
    ComputableInPolyTime (fun x => pivotBasisRows (k x) (d x) (allRows x) (rhsAll x) (T x) (l x))
      encIn (encList encUnary) := by
  unfold pivotBasisRows
  have hfind : ComputableInPolyTime
      (fun x => (List.range (d x)).find? fun c =>
        !decide (c ∈ T x) &&
          isFeasibleBasisRows (k x) (d x) (allRows x) (rhsAll x)
            (replaceSorted (d x) (T x) (l x) c))
      encIn (encOption encUnary) := by
    refine findWithInput (range.comp hd) ?_
    have hx := fst encIn encUnary
    have hc := snd encIn encUnary
    have hrep := replaceSorted_polytime (hd.comp hx) (hT.comp hx) (hl.comp hx) hc
    exact bool_and' (bool_not.comp (decide_mem (hT.comp hx) hc))
      (isFeasibleBasisRows_polytime (hk.comp hx) (hd.comp hx) (hall.comp hx) (hrhs.comp hx) hrep)
  exact optionElimWithInput hfind hT
    (replaceSorted_polytime (hd.comp (fst encIn encUnary)) (hT.comp (fst encIn encUnary))
      (hl.comp (fst encIn encUnary)) (snd encIn encUnary))

private lemma pivotBasisRows_spec {m n k : ℕ}
    (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ) (b_int : Fin m ⊕ Fin n → ℤ)
    (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), rhsAll.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    (hnd : IsNondegenerateSystem (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
      (fun r => (b_int r : ℚ)))
    (hrec : ∀ v : Fin k → ℚ,
      (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ) *ᵥ v ≤ 0 → v = 0)
    {T : List ℕ} (_hsort : T.Pairwise (· < ·)) (_hlt : ∀ r ∈ T, r < m + n) (_hlen : T.length = k)
    (hcard : (finsetOfList m n T).card = k)
    (hfb : IsFeasibleBasis M_int b_int (finsetOfList m n T) hcard)
    {l' : Fin m ⊕ Fin n} (hl' : l' ∈ finsetOfList m n T) :
    let l := (finSumFinEquiv l').1
    let T' := pivotBasisRows k (m + n) allRows rhsAll T l
    let x := ratBasisSol M_int b_int (finsetOfList m n T) hcard
    T'.Pairwise (· < ·) ∧ (∀ r ∈ T', r < m + n) ∧ T'.length = k ∧
      ∃ hcard' : (finsetOfList m n T').card = k,
        IsFeasibleBasis M_int b_int (finsetOfList m n T') hcard' ∧
          finsetOfList m n T' = tightRows (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
            (fun r => (b_int r : ℚ))
            (pivotVertex (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
              (fun r => (b_int r : ℚ)) x l') := by
  intro l T' x
  set M_Q : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ := M_int.map Int.cast
  set b_Q : Fin m ⊕ Fin n → ℚ := fun r => (b_int r : ℚ)
  obtain ⟨hx_v, _⟩ := isVertex_ratBasisSol_of_isFeasibleBasis hfb (K := ℚ)
  have htx : tightRows M_Q b_Q x = finsetOfList m n T := tightRows_ratBasisSol_eq hfb hnd
  have hl_tight : l' ∈ tightRows M_Q b_Q x := htx ▸ hl'
  obtain ⟨hy_v, hyx, hy_sub⟩ := hx_v.pivotVertex_spec hnd hrec hl_tight
  set y := pivotVertex M_Q b_Q x l'
  obtain ⟨hTy, hfb_y, -⟩ := exists_isFeasibleBasis_of_isVertex hnd hy_v
  set T_y := tightRows M_Q b_Q y
  have hTy' : T_y.card = k := hTy
  have hl'_not_y : l' ∉ T_y := hx_v.notMem_tightRows_pivotVertex hnd hrec hl_tight
  have hsub_erase : (finsetOfList m n T).erase l' ⊆ T_y := htx ▸ hy_sub
  have hcard_erase : ((finsetOfList m n T).erase l').card = k - 1 := by
    rw [Finset.card_erase_of_mem hl', hcard]
  have hkpos : 1 ≤ k := by
    rw [← hcard]
    exact Finset.card_pos.2 ⟨l', hl'⟩
  have hcard_sdiff : (T_y \ (finsetOfList m n T).erase l').card = 1 := by
    have hadd := Finset.card_sdiff_add_card_inter T_y ((finsetOfList m n T).erase l')
    have hinter : T_y ∩ (finsetOfList m n T).erase l' = (finsetOfList m n T).erase l' :=
      Finset.inter_eq_right.2 hsub_erase
    rw [hinter, hTy', hcard_erase] at hadd
    omega
  obtain ⟨c', hc'eq⟩ := Finset.card_eq_one.1 hcard_sdiff
  have hc'_sdiff : c' ∈ T_y \ (finsetOfList m n T).erase l' := by simp [hc'eq]
  have hc'_y : c' ∈ T_y := (Finset.mem_sdiff.1 hc'_sdiff).1
  have hc'_not_erase : c' ∉ (finsetOfList m n T).erase l' := (Finset.mem_sdiff.1 hc'_sdiff).2
  have hc'_ne_l' : c' ≠ l' := fun h => hl'_not_y (h ▸ hc'_y)
  have hc'_not_Tset : c' ∉ finsetOfList m n T := fun h =>
    hc'_not_erase (Finset.mem_erase.2 ⟨hc'_ne_l', h⟩)
  have hTy_eq : T_y = insert c' ((finsetOfList m n T).erase l') := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      by_cases hzc : z = c'
      · exact hzc ▸ Finset.mem_insert_self _ _
      · have hzs : z ∈ T_y \ (finsetOfList m n T).erase l' → False := by
          intro hm
          rw [hc'eq, Finset.mem_singleton] at hm
          exact hzc hm
        by_contra hnot
        exact hzs (Finset.mem_sdiff.2 ⟨hz, fun hm => hnot (Finset.mem_insert_of_mem hm)⟩)
    · rw [Finset.card_insert_of_notMem hc'_not_erase, hcard_erase, hTy']
      omega
  set cNat := (finSumFinEquiv c').1
  have hcNat_lt : cNat < m + n := (finSumFinEquiv c').2
  have hcNat_not_T : cNat ∉ T := fun h => hc'_not_Tset (mem_finsetOfList.2 h)
  have hrep_c_fin : finsetOfList m n (replaceSorted (m + n) T l cNat) = T_y := by
    rw [finsetOfList_replaceSorted, hTy_eq]
  have hrep_c_sort : (replaceSorted (m + n) T l cNat).Pairwise (· < ·) :=
    replaceSorted_sorted _ _ _ _
  have hrep_c_lt : ∀ r ∈ replaceSorted (m + n) T l cNat, r < m + n := fun _ hr =>
    replaceSorted_lt hr
  have hrep_c_len : (replaceSorted (m + n) T l cNat).length = k := by
    have hc1 := card_finsetOfList hrep_c_sort.nodup hrep_c_lt
    rw [hrep_c_fin, hTy'] at hc1
    exact hc1.symm
  have hfb_rep_c : IsFeasibleBasis M_int b_int
      (finsetOfList m n (replaceSorted (m + n) T l cNat))
      ((card_finsetOfList hrep_c_sort.nodup hrep_c_lt).trans hrep_c_len) := by
    have hEq := hrep_c_fin
    revert hfb_y
    simp only [hEq]
    exact fun h => h
  have htest_c :
      (!decide (cNat ∈ T) &&
        isFeasibleBasisRows k (m + n) allRows rhsAll (replaceSorted (m + n) T l cNat)) = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hcNat_not_T,
      (isFeasibleBasisRows_iff M_int b_int allRows rhsAll hall hrhs hrep_c_sort hrep_c_lt
        hrep_c_len).2 hfb_rep_c⟩
  set pred := fun c => !decide (c ∈ T) &&
    isFeasibleBasisRows k (m + n) allRows rhsAll (replaceSorted (m + n) T l c)
  have hne_none : (List.range (m + n)).find? pred ≠ none := by
    intro hnone
    have hfalse := (List.find?_eq_none.1 hnone) cNat (List.mem_range.2 hcNat_lt)
    exact hfalse htest_c
  obtain ⟨c₀, hfind⟩ := Option.ne_none_iff_exists'.1 hne_none
  have hT'_eq : T' = replaceSorted (m + n) T l c₀ := by
    dsimp only [T', pivotBasisRows]
    change ((List.range (m + n)).find? pred).elim T (replaceSorted (m + n) T l) = _
    rw [hfind]
    rfl
  have hc₀_mem : c₀ ∈ List.range (m + n) := List.mem_of_find?_eq_some hfind
  have hc₀_lt : c₀ < m + n := List.mem_range.1 hc₀_mem
  have hc₀_pred : pred c₀ = true := List.find?_some hfind
  simp only [pred, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc₀_pred
  obtain ⟨hc₀_not_T, hc₀_feas⟩ := hc₀_pred
  have hT'_sort : T'.Pairwise (· < ·) := hT'_eq ▸ replaceSorted_sorted _ _ _ _
  have hT'_lt : ∀ r ∈ T', r < m + n := fun _ hr => replaceSorted_lt (hT'_eq ▸ hr)
  set c₀' : Fin m ⊕ Fin n := finSumFinEquiv.symm ⟨c₀, hc₀_lt⟩
  have hc₀'_val : (finSumFinEquiv c₀').1 = c₀ :=
    congrArg Fin.val (Equiv.apply_symm_apply finSumFinEquiv ⟨c₀, hc₀_lt⟩)
  have hc₀'_not_Tset : c₀' ∉ finsetOfList m n T := by
    rw [mem_finsetOfList, hc₀'_val]
    exact hc₀_not_T
  have hc₀'_not_erase : c₀' ∉ (finsetOfList m n T).erase l' := fun h =>
    hc₀'_not_Tset (Finset.mem_erase.1 h).2
  have hT'_fin : finsetOfList m n T' = insert c₀' ((finsetOfList m n T).erase l') := by
    rw [hT'_eq, ← hc₀'_val]
    exact finsetOfList_replaceSorted
  have hT'_card : (finsetOfList m n T').card = k := by
    rw [hT'_fin, Finset.card_insert_of_notMem hc₀'_not_erase, hcard_erase]
    omega
  have hT'_len : T'.length = k := (card_finsetOfList hT'_sort.nodup hT'_lt).symm.trans hT'_card
  have hfb_T' : IsFeasibleBasis M_int b_int (finsetOfList m n T')
      ((card_finsetOfList hT'_sort.nodup hT'_lt).trans hT'_len) :=
    (isFeasibleBasisRows_iff M_int b_int allRows rhsAll hall hrhs hT'_sort hT'_lt hT'_len).1
      (hT'_eq ▸ hc₀_feas)
  set z := ratBasisSol M_int b_int (finsetOfList m n T')
    ((card_finsetOfList hT'_sort.nodup hT'_lt).trans hT'_len)
  have hz_v : IsVertex M_Q b_Q z := (isVertex_ratBasisSol_of_isFeasibleBasis hfb_T' (K := ℚ)).1
  have htz : tightRows M_Q b_Q z = finsetOfList m n T' := tightRows_ratBasisSol_eq hfb_T' hnd
  have hzx : z ≠ x := by
    intro hzx
    have hc₀_in_tz : c₀' ∈ tightRows M_Q b_Q z := by
      rw [htz, hT'_fin]
      exact Finset.mem_insert_self _ _
    rw [hzx, htx] at hc₀_in_tz
    exact hc₀'_not_Tset hc₀_in_tz
  have hz_erase : (tightRows M_Q b_Q x).erase l' ⊆ tightRows M_Q b_Q z := by
    rw [htx, htz, hT'_fin]
    exact Finset.subset_insert _ _
  have hzy : z = y := hx_v.eq_pivotVertex hnd hrec hl_tight hz_v hzx hz_erase
  refine ⟨hT'_sort, hT'_lt, hT'_len, hT'_card, hfb_T', ?_⟩
  rw [← htz, hzy]

/-- Executable tie-breaking leaving label matching `ShapleyOrientation.leaveLabel` for `k₀ = 0`. -/
private def leaveLabelExec (T₁ T₂ : List ℕ) : ℕ :=
  if decide (0 ∈ T₁) || decide (0 ∈ T₂) then 0
  else (T₁.filter fun x => decide (x ∈ T₂)).getD 0 0

private theorem leaveLabelExec_polytime {α : Type} {encIn : α ↪ List Bool}
    {T₁ T₂ : α → List ℕ}
    (h1 : ComputableInPolyTime T₁ encIn (encList encUnary))
    (h2 : ComputableInPolyTime T₂ encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => leaveLabelExec (T₁ x) (T₂ x)) encIn encUnary := by
  unfold leaveLabelExec
  refine ite' (bool_or' (decide_mem h1 (const 0)) (decide_mem h2 (const 0))) (const 0) ?_
  have hfilt : ComputableInPolyTime
      (fun x => (T₁ x).filter fun y => decide (y ∈ T₂ x)) encIn (encList encUnary) :=
    filterWithInput h1 (decide_mem (h2.comp (fst _ _)) (snd _ _))
  exact listGetDWithInput hfilt (const 0) 0

private lemma leaveLabelExec_eq {m n : ℕ} (hm : 0 < m)
    {T₁ T₂ : List ℕ} (hsort₁ : T₁.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ T₁, r < m + n) (_hlt₂ : ∀ r ∈ T₂, r < m + n) :
    (finSumFinEquiv (LemkeHowson.leaveLabel (finsetOfList m n T₁) (finsetOfList m n T₂)
      (Sum.inl ⟨0, hm⟩))).1 = leaveLabelExec T₁ T₂ := by
  set T₁s := finsetOfList m n T₁
  set T₂s := finsetOfList m n T₂
  set k₀ : Fin m ⊕ Fin n := Sum.inl ⟨0, hm⟩
  have hk₀_val : (finSumFinEquiv k₀).1 = 0 := rfl
  have hk₀_mem : k₀ ∈ T₁s ∪ T₂s ↔ 0 ∈ T₁ ∨ 0 ∈ T₂ := by
    simp only [Finset.mem_union, T₁s, T₂s, mem_finsetOfList, hk₀_val]
  by_cases h0 : 0 ∈ T₁ ∨ 0 ∈ T₂
  · have hmem : k₀ ∈ T₁s ∪ T₂s := hk₀_mem.2 h0
    have h1 : LemkeHowson.leaveLabel T₁s T₂s k₀ = k₀ := by
      simp only [LemkeHowson.leaveLabel, ite_eq_left hmem]
    have h2 : leaveLabelExec T₁ T₂ = 0 := by
      simp only [leaveLabelExec, Bool.or_eq_true, decide_eq_true_eq, ite_eq_left h0]
    rw [h1, h2, hk₀_val]
  · have hnmem : k₀ ∉ T₁s ∪ T₂s := fun h => h0 (hk₀_mem.1 h)
    have h2 : leaveLabelExec T₁ T₂ = (T₁.filter fun x => decide (x ∈ T₂)).getD 0 0 := by
      simp only [leaveLabelExec, Bool.or_eq_true, decide_eq_true_eq, ite_eq_right h0]
    rw [LemkeHowson.leaveLabel, ite_eq_right hnmem, h2]
    by_cases hne : (T₁s ∩ T₂s).Nonempty
    · rw [dite_eq_left hne]
      have hmin_mem : (T₁s ∩ T₂s).min' hne ∈ T₁s ∩ T₂s := Finset.min'_mem _ hne
      set min_v := (finSumFinEquiv ((T₁s ∩ T₂s).min' hne)).1
      have hmin_T1 : min_v ∈ T₁ := mem_finsetOfList.1 (Finset.mem_inter.1 hmin_mem).1
      have hmin_T2 : min_v ∈ T₂ := mem_finsetOfList.1 (Finset.mem_inter.1 hmin_mem).2
      set F := T₁.filter fun x => decide (x ∈ T₂)
      have hmin_F : min_v ∈ F := List.mem_filter.2 ⟨hmin_T1, decide_eq_true hmin_T2⟩
      have hF_ne : F ≠ [] := List.ne_nil_of_mem hmin_F
      have hF_sort : F.Pairwise (· < ·) := hsort₁.filter _
      rcases hFc : F with _ | ⟨a, rest⟩
      · exact absurd hFc hF_ne
      · have hhead : (a :: rest).getD 0 0 = a := rfl
        have ha_mem_F : a ∈ F := hFc ▸ List.mem_cons_self
        have ha_T1 : a ∈ T₁ := (List.mem_filter.1 ha_mem_F).1
        have ha_T2 : a ∈ T₂ := of_decide_eq_true (List.mem_filter.1 ha_mem_F).2
        have ha_lt : a < m + n := hlt₁ a ha_T1
        set a' : Fin m ⊕ Fin n := finSumFinEquiv.symm ⟨a, ha_lt⟩
        have ha'_val : (finSumFinEquiv a').1 = a :=
          congrArg Fin.val (Equiv.apply_symm_apply finSumFinEquiv ⟨a, ha_lt⟩)
        have ha'_mem : a' ∈ T₁s ∩ T₂s := Finset.mem_inter.2
          ⟨mem_finsetOfList.2 (ha'_val.symm ▸ ha_T1), mem_finsetOfList.2 (ha'_val.symm ▸ ha_T2)⟩
        have hle1 : (T₁s ∩ T₂s).min' hne ≤ a' := Finset.min'_le _ a' ha'_mem
        have hle1_nat : min_v ≤ a := by
          change (finSumFinEquiv ((T₁s ∩ T₂s).min' hne)).1 ≤ (finSumFinEquiv a').1 at hle1
          rwa [ha'_val] at hle1
        have hle2_nat : a ≤ min_v := by
          by_cases heqm : a = min_v
          · exact heqm.le
          · have hmin_rest : min_v ∈ a :: rest := hFc ▸ hmin_F
            rcases List.mem_cons.1 hmin_rest with h | h
            · exact absurd h.symm heqm
            · have hp := hFc ▸ hF_sort
              exact ((List.pairwise_cons.1 hp).1 min_v h).le
        rw [hhead]
        exact le_antisymm hle1_nat hle2_nat
    · rw [dite_eq_right hne]
      have hF_empty : (T₁.filter fun x => decide (x ∈ T₂)) = [] := by
        by_contra hneF
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hneF
        have ha_T1 : a ∈ T₁ := (List.mem_filter.1 ha).1
        have ha_T2 : a ∈ T₂ := of_decide_eq_true (List.mem_filter.1 ha).2
        have ha_lt : a < m + n := hlt₁ a ha_T1
        set a' := finSumFinEquiv.symm ⟨a, ha_lt⟩
        have ha'_val : (finSumFinEquiv a').1 = a :=
          congrArg Fin.val (Equiv.apply_symm_apply finSumFinEquiv ⟨a, ha_lt⟩)
        exact hne ⟨a', Finset.mem_inter.2
          ⟨mem_finsetOfList.2 (ha'_val.symm ▸ ha_T1), mem_finsetOfList.2 (ha'_val.symm ▸ ha_T2)⟩⟩
      rw [hF_empty, List.getD_nil, hk₀_val]

/-- Image of `ShapleyOrientation.halfEdgeFun` on `[0 .. m+n-1]` for `k₀ = 0`. -/
private def halfEdgeList (T₁ T₂ : List ℕ) (side : Bool) : List ℕ :=
  let l := leaveLabelExec T₁ T₂
  (if !side then T₁.map fun x => if decide (x = l) then 0 else x else T₁) ++
    (if side then T₂.map fun x => if decide (x = l) then 0 else x else T₂)

private theorem halfEdgeList_polytime {α : Type} {encIn : α ↪ List Bool}
    {T₁ T₂ : α → List ℕ} {side : α → Bool}
    (h1 : ComputableInPolyTime T₁ encIn (encList encUnary))
    (h2 : ComputableInPolyTime T₂ encIn (encList encUnary))
    (hs : ComputableInPolyTime side encIn encBool) :
    ComputableInPolyTime (fun x => halfEdgeList (T₁ x) (T₂ x) (side x))
      encIn (encList encUnary) := by
  have hl := leaveLabelExec_polytime h1 h2
  have hmap : ∀ (T : α → List ℕ),
      ComputableInPolyTime T encIn (encList encUnary) →
      ComputableInPolyTime (fun x => (T x).map fun y =>
        if decide (y = leaveLabelExec (T₁ x) (T₂ x)) then 0 else y) encIn (encList encUnary) := by
    intro T hT
    refine mapWithInput hT ?_
    exact ite' (decide_eq' (snd _ _) (hl.comp (fst _ _))) (const 0) (snd _ _)
  unfold halfEdgeList
  exact listAppend' (ite' (bool_not.comp hs) (hmap T₁ h1) h1) (ite' hs (hmap T₂ h2) h2)

/-- `d × d` permutation matrix rows for index list `L`. -/
private def permRows (d : ℕ) (L : List ℕ) : List (List ℤ) :=
  tabulateTable d d fun i j => if decide (L.getD i 0 = j) then 1 else 0

private theorem permRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {d : α → ℕ} {L : α → List ℕ}
    (hd : ComputableInPolyTime d encIn encUnary)
    (hL : ComputableInPolyTime L encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => permRows (d x) (L x)) encIn encIntTable := by
  unfold permRows
  refine computableInPolyTime_tabulateTable hd hd ?_
  have hx := (fst encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)
  have hi := (snd encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)
  have hj := snd (encPair encIn encUnary) encUnary
  exact ite' (decide_eq' (listGetDWithInput (hL.comp hx) hi 0) hj)
    (const (encOut := encIntBin) 1) (const (encOut := encIntBin) 0)

private lemma detRows_permRows {d : ℕ} (σ : Equiv.Perm (Fin d)) {L : List ℕ}
    (hL : ∀ i : Fin d, (σ i).1 = L.getD i.1 0) :
    detRows (permRows d L) = (Equiv.Perm.sign σ : ℤ) := by
  have hlen : (permRows d L).length = d := by simp [permRows, tabulateTable]
  have hentry : ∀ i j : Fin d,
      rowEntry (permRows d L) i.1 j.1 = ((1 : Matrix (Fin d) (Fin d) ℤ).submatrix σ id) i j := by
    intro i j
    dsimp only [permRows]
    rw [rowEntry_tabulateTable, ite_eq_left ⟨i.2, j.2⟩, Matrix.submatrix_apply, id_eq,
      Matrix.one_apply, ← hL i]
    by_cases hij : σ i = j
    · have hij' : (σ i).1 = j.1 := congrArg Fin.val hij
      rw [ite_eq_left hij, ite_eq_left (decide_eq_true hij')]
    · have hij' : (σ i).1 ≠ j.1 := fun h => hij (Fin.ext h)
      rw [ite_eq_right hij, ite_eq_right (by simp [hij'])]
  rw [detRows_eq_det_of_rowEntry _ hlen hentry, Matrix.det_permute, Matrix.det_one]
  change (Equiv.Perm.sign σ : ℤ) * 1 = _
  rw [mul_one]

/-- Executable Shapley orientation index in `{-1, 0, 1}` using integer determinants. -/
private def halfEdgeIndexExec (c : BimatrixCode) (T₁ T₂ : List ℕ) (side : Bool) : ℤ :=
  let d := c.rows + c.cols
  let M₁ := subRows c.rows (allRowsP c) T₁
  let M₂ := subRows c.cols (allRowsQ c) T₂
  detRows (permRows d (halfEdgeList T₁ T₂ side)) * (detRows M₁).sign * (detRows M₂).sign

private theorem halfEdgeIndexExec_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {T₁ T₂ : α → List ℕ} {side : α → Bool}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (h1 : ComputableInPolyTime T₁ encIn (encList encUnary))
    (h2 : ComputableInPolyTime T₂ encIn (encList encUnary))
    (hs : ComputableInPolyTime side encIn encBool) :
    ComputableInPolyTime (fun x => halfEdgeIndexExec (c x) (T₁ x) (T₂ x) (side x))
      encIn encIntBin := by
  unfold halfEdgeIndexExec
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hd := unary_add.comp (hm.prod hn)
  have hperm := detRows_polytime.comp (permRows_polytime hd (halfEdgeList_polytime h1 h2 hs))
  have hm1 := detRows_polytime.comp
    (subRows_polytime hm (allRowsP_polytime.comp hc) h1)
  have hm2 := detRows_polytime.comp
    (subRows_polytime hn (allRowsQ_polytime.comp hc) h2)
  exact intBin_mul' (intBin_mul' hperm (intBin_sign.comp hm1)) (intBin_sign.comp hm2)

private lemma halfEdgeIndexExec_eq (c : BimatrixCode) (hm : 0 < c.rows)
    {T₁ T₂ : List ℕ} (hsort₁ : T₁.Pairwise (· < ·)) (hsort₂ : T₂.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ T₁, r < c.rows + c.cols) (hlt₂ : ∀ r ∈ T₂, r < c.rows + c.cols)
    (hlen₁ : T₁.length = c.rows) (hlen₂ : T₂.length = c.cols) (side : Bool)
    (hacl : ∀ k : Fin c.rows ⊕ Fin c.cols,
      k ≠ .inl ⟨0, hm⟩ → k ∈ finsetOfList c.rows c.cols T₁ ∨ k ∈ finsetOfList c.rows c.cols T₂)
    (hact : if side then .inl ⟨0, hm⟩ ∉ finsetOfList c.rows c.cols T₁
      else .inl ⟨0, hm⟩ ∉ finsetOfList c.rows c.cols T₂) :
    have hcard₁ : (finsetOfList c.rows c.cols T₁).card = c.rows :=
      (card_finsetOfList hsort₁.nodup hlt₁).trans hlen₁
    have hcard₂ : (finsetOfList c.rows c.cols T₂).card = c.cols :=
      (card_finsetOfList hsort₂.nodup hlt₂).trans hlen₂
    halfEdgeIndexExec c T₁ T₂ side =
      LemkeHowson.halfEdgeIndex
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
        (finsetOfList c.rows c.cols T₁) (finsetOfList c.rows c.cols T₂)
        hcard₁ hcard₂ (.inl ⟨0, hm⟩) side := by
  intro hcard₁ hcard₂
  set T₁s := finsetOfList c.rows c.cols T₁
  set T₂s := finsetOfList c.rows c.cols T₂
  set k₀ : Fin c.rows ⊕ Fin c.cols := .inl ⟨0, hm⟩
  have hbij : Function.Bijective (LemkeHowson.halfEdgeFun T₁s T₂s hcard₁ hcard₂ k₀ side) :=
    LemkeHowson.halfEdgeFun_bijective_of_acl (Fintype.card_sum.trans (by simp)) hcard₁ hcard₂
      hacl hact
  rw [LemkeHowson.halfEdgeIndex, dite_eq_left hbij]
  dsimp only
  set π : Equiv.Perm (Fin c.rows ⊕ Fin c.cols) :=
    (Equiv.ofBijective _ hbij).trans (Equiv.refl _).symm
  set σ : Equiv.Perm (Fin (c.rows + c.cols)) := Equiv.permCongr finSumFinEquiv π
  have hσ_sign : (Equiv.Perm.sign σ : ℤ) = (Equiv.Perm.sign π : ℤ) := by
    rw [Equiv.Perm.sign_permCongr]
  have hleave := leaveLabelExec_eq hm hsort₁ hlt₁ hlt₂
  have hσ_list : ∀ i : Fin (c.rows + c.cols),
      (σ i).1 = (halfEdgeList T₁ T₂ side).getD i.1 0 := by
    intro i
    change (finSumFinEquiv (LemkeHowson.halfEdgeFun T₁s T₂s hcard₁ hcard₂ k₀ side
      (finSumFinEquiv.symm i))).1 = (halfEdgeList T₁ T₂ side).getD i.1 0
    have hmap_len : ∀ (T : List ℕ) (f : ℕ → ℕ), (T.map f).length = T.length := by simp
    have hlhs_len :
        (if !side then T₁.map fun x => if decide (x = leaveLabelExec T₁ T₂) then 0 else x
          else T₁).length = c.rows := by
      cases side <;> simp [hlen₁]
    by_cases hi : i.1 < c.rows
    · have hi' : i = ⟨i.1, by omega⟩ := Fin.ext rfl
      rw [hi', finSumFinEquiv_symm_of_lt hi]
      have hget_app : (halfEdgeList T₁ T₂ side).getD i.1 0 =
          (if !side then T₁.map fun x => if decide (x = leaveLabelExec T₁ T₂) then 0 else x
            else T₁).getD i.1 0 :=
        List.getD_append _ _ 0 i.1 (by rw [hlhs_len]; exact hi)
      rw [hget_app]
      have hord := orderIsoOfFin_finsetOfList hsort₁ hlt₁ hlen₁ hcard₁ ⟨i.1, hi⟩
      cases side
      · simp only [LemkeHowson.halfEdgeFun, Sum.elim_inl, Bool.not_false, ↓reduceIte]
        rw [list_getD_map_lt _ T₁ 0 0 (by rw [hlen₁]; exact hi)]
        have hiff : (T₁s.orderIsoOfFin hcard₁ ⟨i.1, hi⟩).1 = LemkeHowson.leaveLabel T₁s T₂s k₀ ↔
            T₁.getD i.1 0 = leaveLabelExec T₁ T₂ :=
          ⟨fun h => by rw [← hord, h, hleave],
           fun h => finSumFinEquiv.injective (Fin.ext (hord.trans (h.trans hleave.symm)))⟩
        by_cases hc_eq : T₁.getD i.1 0 = leaveLabelExec T₁ T₂
        · have hk : ((T₁s.orderIsoOfFin hcard₁).toEquiv ⟨i.1, hi⟩ :
              Fin c.rows ⊕ Fin c.cols) = LemkeHowson.leaveLabel T₁s T₂s k₀ := hiff.2 hc_eq
          rw [ite_eq_left hk, ite_eq_left (decide_eq_true hc_eq)]
          rfl
        · have hne_k : ((T₁s.orderIsoOfFin hcard₁).toEquiv ⟨i.1, hi⟩ : Fin c.rows ⊕ Fin c.cols) ≠
              LemkeHowson.leaveLabel T₁s T₂s k₀ := fun h => hc_eq (hiff.1 h)
          have hne_c : decide (T₁.getD i.1 0 = leaveLabelExec T₁ T₂) ≠ true := fun h =>
            hc_eq (of_decide_eq_true h)
          rw [ite_eq_right hne_k, ite_eq_right hne_c]
          exact hord
      · simp only [LemkeHowson.halfEdgeFun, Sum.elim_inl, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
        exact hord
    · have hge : c.rows ≤ i.1 := Nat.le_of_not_lt hi
      rw [finSumFinEquiv_symm_of_le hge i.2]
      have hget_app : (halfEdgeList T₁ T₂ side).getD i.1 0 =
          (if side then T₂.map fun x => if decide (x = leaveLabelExec T₁ T₂) then 0 else x
            else T₂).getD (i.1 - c.rows) 0 := by
        dsimp only [halfEdgeList]
        rw [List.getD_append_right _ _ 0 i.1 (by rw [hlhs_len]; exact hge), hlhs_len]
      rw [hget_app]
      have hsub : i.1 - c.rows < c.cols := by omega
      have hord := orderIsoOfFin_finsetOfList hsort₂ hlt₂ hlen₂ hcard₂ ⟨i.1 - c.rows, hsub⟩
      cases side
      · simp only [LemkeHowson.halfEdgeFun, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]
        exact hord
      · simp only [LemkeHowson.halfEdgeFun, Sum.elim_inr, ↓reduceIte]
        rw [list_getD_map_lt _ T₂ 0 0 (by rw [hlen₂]; exact hsub)]
        have hiff : (T₂s.orderIsoOfFin hcard₂ ⟨i.1 - c.rows, hsub⟩).1 =
              LemkeHowson.leaveLabel T₁s T₂s k₀ ↔
            T₂.getD (i.1 - c.rows) 0 = leaveLabelExec T₁ T₂ :=
          ⟨fun h => by rw [← hord, h, hleave],
           fun h => finSumFinEquiv.injective (Fin.ext (hord.trans (h.trans hleave.symm)))⟩
        by_cases hc_eq : T₂.getD (i.1 - c.rows) 0 = leaveLabelExec T₁ T₂
        · have hk : ((T₂s.orderIsoOfFin hcard₂).toEquiv ⟨i.1 - c.rows, hsub⟩ :
              Fin c.rows ⊕ Fin c.cols) = LemkeHowson.leaveLabel T₁s T₂s k₀ := hiff.2 hc_eq
          rw [ite_eq_left hk, ite_eq_left (decide_eq_true hc_eq)]
          rfl
        · have hne_k : ((T₂s.orderIsoOfFin hcard₂).toEquiv ⟨i.1 - c.rows, hsub⟩ :
              Fin c.rows ⊕ Fin c.cols) ≠ LemkeHowson.leaveLabel T₁s T₂s k₀ :=
            fun h => hc_eq (hiff.1 h)
          have hne_c : decide (T₂.getD (i.1 - c.rows) 0 = leaveLabelExec T₁ T₂) ≠ true :=
            fun h => hc_eq (of_decide_eq_true h)
          rw [ite_eq_right hne_k, ite_eq_right hne_c]
          exact hord
  have hdet_perm : detRows (permRows (c.rows + c.cols) (halfEdgeList T₁ T₂ side)) =
      (Equiv.Perm.sign π : ℤ) :=
    (detRows_permRows σ hσ_list).trans hσ_sign
  have hsub₁ := subRows_eq_basisMat (intMatP (posMatB c)) (allRowsP c) (allRowsP_spec c)
    hsort₁ hlt₁ hlen₁
  have hsub₂ := subRows_eq_basisMat (intMatQ (posMatA c)) (allRowsQ c) (allRowsQ_spec c)
    hsort₂ hlt₂ hlen₂
  have hm₁_det :
      (((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ).submatrix
        (fun i => (T₁s.orderIsoOfFin hcard₁ i : Fin c.rows ⊕ Fin c.cols)) (Equiv.refl _)).det =
        ((basisMat (intMatP (posMatB c)) T₁s hcard₁).det : ℚ) := by
    rw [show ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ).submatrix
          (fun i => (T₁s.orderIsoOfFin hcard₁ i : Fin c.rows ⊕ Fin c.cols)) (Equiv.refl _) =
          (basisMat (intMatP (posMatB c)) T₁s hcard₁).map Int.cast from rfl, ← Int.cast_det]
  have hm₂_det :
      (((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ).submatrix
        (fun j => (T₂s.orderIsoOfFin hcard₂ j : Fin c.rows ⊕ Fin c.cols)) (Equiv.refl _)).det =
        ((basisMat (intMatQ (posMatA c)) T₂s hcard₂).det : ℚ) := by
    rw [show ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ).submatrix
          (fun j => (T₂s.orderIsoOfFin hcard₂ j : Fin c.rows ⊕ Fin c.cols)) (Equiv.refl _) =
          (basisMat (intMatQ (posMatA c)) T₂s hcard₂).map Int.cast from rfl, ← Int.cast_det]
  dsimp only [halfEdgeIndexExec]
  dsimp only [T₁s, T₂s] at hbij hm₁_det hm₂_det ⊢
  rw [hdet_perm, hsub₁.2.2, hsub₂.2.2, hm₁_det, hm₂_det,
    LemkeHowson.signOfK_intCast, LemkeHowson.signOfK_intCast]

/-- Executable check that `u` encodes a valid `k₀ = 0`-almost-completely-labelled basis pair. -/
private def isValidNodeExec (c : BimatrixCode) (u : List Bool) : Bool :=
  let d := c.rows + c.cols
  let T₁ := decodeT₁ c u
  let T₂ := decodeT₂ c u
  c.wellFormedB &&
  decide (u.length = 2 * d) &&
  decide (T₁.length = c.rows) &&
  decide (T₂.length = c.cols) &&
  ((List.range d).all fun k => decide (k = 0) || decide (k ∈ T₁) || decide (k ∈ T₂)) &&
  isFeasibleBasisRows c.rows d (allRowsP c) (allRhsP c) T₁ &&
  isFeasibleBasisRows c.cols d (allRowsQ c) (allRhsQ c) T₂

@[local fun_prop]
private theorem isValidNodeExec_polytime :
    ComputableInPolyTime (fun p : BimatrixCode × List Bool => isValidNodeExec p.1 p.2)
      (encPair encBimatrix encBits) encBool := by
  unfold isValidNodeExec
  have hc := fst encBimatrix encBits
  have hu := snd encBimatrix encBits
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hd := unary_add.comp (hm.prod hn)
  have h1 := decodeT₁_polytime
  have h2 := decodeT₂_polytime
  have hall : ComputableInPolyTime
      (fun p : BimatrixCode × List Bool =>
        (List.range (p.1.rows + p.1.cols)).all fun k =>
          decide (k = 0) || decide (k ∈ decodeT₁ p.1 p.2) || decide (k ∈ decodeT₂ p.1 p.2))
      (encPair encBimatrix encBits) encBool := by
    refine allWithInput (range.comp hd) ?_
    have hp := fst (encPair encBimatrix encBits) encUnary
    have hk := snd (encPair encBimatrix encBits) encUnary
    exact bool_or' (bool_or' (decide_eq' hk (const 0)) (decide_mem (h1.comp hp) hk))
      (decide_mem (h2.comp hp) hk)
  have hf1 := isFeasibleBasisRows_polytime hm hd (allRowsP_polytime.comp hc)
    (allRhsP_polytime.comp hc) h1
  have hf2 := isFeasibleBasisRows_polytime hn hd (allRowsQ_polytime.comp hc)
    (allRhsQ_polytime.comp hc) h2
  refine bool_and' (bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
    (wellFormedB_polytime.comp hc)
    (decide_eq' (length_bits.comp hu) (unary_mul.comp ((const 2).prod hd))))
    (decide_eq' ((length_list encUnary).comp h1) hm))
    (decide_eq' ((length_list encUnary).comp h2) hn))
    hall) hf1) hf2

/-- Follow the active half-edge with orientation `-targetSign c` (`wantNeg = true`) or
`targetSign c` (`wantNeg = false`), fixing non-valid or non-matching nodes. -/
private def stepGraph (wantNeg : Bool) (c : BimatrixCode) (u : List Bool) : List Bool :=
  if !isValidNodeExec c u then u
  else
    let d := c.rows + c.cols
    let T₁ := decodeT₁ c u
    let T₂ := decodeT₂ c u
    let wanted := if wantNeg then -targetSign c else targetSign c
    let l := leaveLabelExec T₁ T₂
    if !decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁ T₂ false = wanted) then
      encodeNodes c (pivotBasisRows c.rows d (allRowsP c) (allRhsP c) T₁ l) T₂
    else if !decide (0 ∈ T₁) && decide (halfEdgeIndexExec c T₁ T₂ true = wanted) then
      encodeNodes c T₁ (pivotBasisRows c.cols d (allRowsQ c) (allRhsQ c) T₂ l)
    else u

/-- Polynomial-time predecessor map on encoded Lemke–Howson graph nodes (`-targetSign c`). -/
def pred (p : BimatrixCode × List Bool) : List Bool := stepGraph true p.1 p.2

/-- Polynomial-time successor map on encoded Lemke–Howson graph nodes (`+targetSign c`). -/
def succ (p : BimatrixCode × List Bool) : List Bool := stepGraph false p.1 p.2

private theorem stepGraph_polytime (wantNeg : Bool) :
    ComputableInPolyTime (fun p : BimatrixCode × List Bool => stepGraph wantNeg p.1 p.2)
      (encPair encBimatrix encBits) encBits := by
  unfold stepGraph
  have hc := fst encBimatrix encBits
  have hu := snd encBimatrix encBits
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hd := unary_add.comp (hm.prod hn)
  have h1 := decodeT₁_polytime
  have h2 := decodeT₂_polytime
  have hts := targetSign_polytime.comp hc
  have hwanted : ComputableInPolyTime
      (fun p : BimatrixCode × List Bool =>
        if wantNeg then -targetSign p.1 else targetSign p.1)
      (encPair encBimatrix encBits) encIntBin := by
    cases wantNeg
    · exact hts.of_enc_eq fun _ => rfl
    · exact (intBin_sub' (const 0) hts).of_enc_eq fun _ => by simp
  have hl := leaveLabelExec_polytime h1 h2
  have hidxL := halfEdgeIndexExec_polytime hc h1 h2 (const false)
  have hidxR := halfEdgeIndexExec_polytime hc h1 h2 (const true)
  have hpiv1 := pivotBasisRows_polytime hm hd (allRowsP_polytime.comp hc)
    (allRhsP_polytime.comp hc) h1 hl
  have hpiv2 := pivotBasisRows_polytime hn hd (allRowsQ_polytime.comp hc)
    (allRhsQ_polytime.comp hc) h2 hl
  have hleft := bool_and' (bool_not.comp (decide_mem h2 (const 0))) (decide_eq' hidxL hwanted)
  have hright := bool_and' (bool_not.comp (decide_mem h1 (const 0))) (decide_eq' hidxR hwanted)
  exact ite' (bool_not.comp isValidNodeExec_polytime) hu
    (ite' hleft (encodeNodes_polytime hc hpiv1 h2)
      (ite' hright (encodeNodes_polytime hc h1 hpiv2) hu))

private theorem pred_polytime :
    ComputableInPolyTime pred (encPair encBimatrix encBits) encBits :=
  stepGraph_polytime true

private theorem succ_polytime :
    ComputableInPolyTime succ (encPair encBimatrix encBits) encBits :=
  stepGraph_polytime false

private lemma length_stepGraph (wantNeg : Bool) (c : BimatrixCode) (u : List Bool)
    (hu : u.length = vertexLen c) : (stepGraph wantNeg c u).length = vertexLen c := by
  dsimp only [stepGraph]
  by_cases hv : isValidNodeExec c u = true
  · have hwf : c.wellFormedB = true := by
      simp only [isValidNodeExec, Bool.and_eq_true] at hv
      exact hv.1.1.1.1.1.1
    have hnotv : (!isValidNodeExec c u) = false := by simp [hv]
    rw [ite_eq_right (by simp [hnotv])]
    split_ifs <;> simp [length_encodeNodes, vertexLen, hwf, hu]
  · have hnotv : (!isValidNodeExec c u) = true := by cases h : isValidNodeExec c u <;> simp_all
    rw [ite_eq_left hnotv]
    exact hu

private lemma length_pred (c : BimatrixCode) (u : List Bool) (hu : u.length = vertexLen c) :
    (pred (c, u)).length = vertexLen c :=
  length_stepGraph true c u hu

private lemma length_succ (c : BimatrixCode) (u : List Bool) (hu : u.length = vertexLen c) :
    (succ (c, u)).length = vertexLen c :=
  length_stepGraph false c u hu

private lemma isValidNodeExec_zeroVertex {c : BimatrixCode} (hc : c.WellFormed) :
    isValidNodeExec c (zeroVertex (vertexLen c)) = true := by
  have hwb : c.wellFormedB = true := (wellFormed_iff_wellFormedB c).1 hc
  have hvlen : vertexLen c = 2 * (c.rows + c.cols) := by simp [vertexLen, hwb]
  have hT₁_eq : decodeT₁ c (zeroVertex (2 * (c.rows + c.cols))) = List.range c.rows :=
    decodeT₁_zeroVertex c
  have hT₂_eq : decodeT₂ c (zeroVertex (2 * (c.rows + c.cols))) =
      (List.range c.cols).map (· + c.rows) := decodeT₂_zeroVertex c
  have hsort₁ : (List.range c.rows).Pairwise (· < ·) := List.pairwise_lt_range
  have hsort₂ : ((List.range c.cols).map (· + c.rows)).Pairwise (· < ·) :=
    List.pairwise_lt_range.map _ fun _ _ h => by omega
  have hlt₁ : ∀ r ∈ List.range c.rows, r < c.rows + c.cols := fun r hr => by
    rw [List.mem_range] at hr; omega
  have hlt₂ : ∀ r ∈ (List.range c.cols).map (· + c.rows), r < c.rows + c.cols := by
    intro r hr
    rcases List.mem_map.1 hr with ⟨j, hj, rfl⟩
    rw [List.mem_range] at hj
    omega
  have hlen₁ : (List.range c.rows).length = c.rows := List.length_range
  have hlen₂ : ((List.range c.cols).map (· + c.rows)).length = c.cols := by simp
  have hcard₁ : (finsetOfList c.rows c.cols (List.range c.rows)).card = c.rows :=
    (card_finsetOfList hsort₁.nodup hlt₁).trans hlen₁
  have hcard₂ : (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))).card =
      c.cols := (card_finsetOfList hsort₂.nodup hlt₂).trans hlen₂
  have ho₁ (i : Fin c.rows) :
      ((finsetOfList c.rows c.cols (List.range c.rows)).orderIsoOfFin hcard₁ i).1 = Sum.inl i := by
    have ho := orderIsoOfFin_finsetOfList hsort₁ hlt₁ hlen₁ hcard₁ i
    rw [List.getD_eq_getElem _ 0 (by simp [i.2]), List.getElem_range] at ho
    apply finSumFinEquiv.injective
    ext
    exact ho
  have ho₂ (i : Fin c.cols) :
      ((finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))).orderIsoOfFin
        hcard₂ i).1 = Sum.inr i := by
    have ho := orderIsoOfFin_finsetOfList hsort₂ hlt₂ hlen₂ hcard₂ i
    rw [List.getD_map_range _ 0 i.2] at ho
    apply finSumFinEquiv.injective
    ext
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
    omega
  have hB₁_neg : basisMat (intMatP (posMatB c))
      (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁ = -1 := by
    ext i j
    dsimp only [basisMat, Matrix.submatrix_apply, id_eq]
    rw [ho₁ i, intMatP_inl]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hB₂_neg : basisMat (intMatQ (posMatA c))
      (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂ = -1 := by
    ext i j
    dsimp only [basisMat, Matrix.submatrix_apply, id_eq]
    rw [ho₂ i, intMatQ_inr]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hfb₁ : IsFeasibleBasis (intMatP (posMatB c))
      (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
      (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁ := by
    have hdet : (basisMat (intMatP (posMatB c))
        (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁).det ≠ 0 := by
      rw [hB₁_neg, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]
      exact pow_ne_zero _ (by decide)
    have hcv : cramerVec (intMatP (posMatB c))
        (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁ = 0 := by
      have hmul : (basisMat (intMatP (posMatB c))
          (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁) *ᵥ
            cramerVec (intMatP (posMatB c))
              (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
              (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁ = 0 := by
        dsimp only [cramerVec]
        rw [Matrix.mulVec_cramer]
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ho₁ i, pertRhsPInt, Sum.elim_inl,
          mul_zero]
      rw [hB₁_neg, Matrix.neg_mulVec, Matrix.one_mulVec, neg_eq_zero] at hmul
      exact hmul
    refine ⟨hdet, fun r => ?_⟩
    rw [hcv, dotProduct_zero, mul_zero]
    have hD_pos : 0 ≤ |(basisMat (intMatP (posMatB c))
        (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁).det| := abs_nonneg _
    have hK_nn : 0 ≤ pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r := by
      cases r <;> simp only [pertRhsPInt, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, le_refl]
      positivity
    exact mul_nonneg hD_pos hK_nn
  have hfb₂ : IsFeasibleBasis (intMatQ (posMatA c))
      (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
      (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂ := by
    have hdet : (basisMat (intMatQ (posMatA c))
        (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂).det ≠ 0 := by
      rw [hB₂_neg, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]
      exact pow_ne_zero _ (by decide)
    have hcv : cramerVec (intMatQ (posMatA c))
        (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂ = 0 := by
      have hmul : (basisMat (intMatQ (posMatA c))
          (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂) *ᵥ
            cramerVec (intMatQ (posMatA c))
              (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
              (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂ = 0 := by
        dsimp only [cramerVec]
        rw [Matrix.mulVec_cramer]
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ho₂ i, pertRhsQInt, Sum.elim_inr,
          mul_zero]
      rw [hB₂_neg, Matrix.neg_mulVec, Matrix.one_mulVec, neg_eq_zero] at hmul
      exact hmul
    refine ⟨hdet, fun r => ?_⟩
    rw [hcv, dotProduct_zero, mul_zero]
    have hD_pos : 0 ≤ |(basisMat (intMatQ (posMatA c))
        (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂).det| :=
      abs_nonneg _
    have hK_nn : 0 ≤ pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r := by
      cases r <;> simp only [pertRhsQInt, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, le_refl]
      positivity
    exact mul_nonneg hD_pos hK_nn
  have hf1 : isFeasibleBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c)
      (List.range c.rows) = true :=
    (isFeasibleBasisRows_iff _ _ (allRowsP c) (allRhsP c) (allRowsP_spec c) (allRhsP_spec c)
      hsort₁ hlt₁ hlen₁).2 hfb₁
  have hf2 : isFeasibleBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c)
      ((List.range c.cols).map (· + c.rows)) = true :=
    (isFeasibleBasisRows_iff _ _ (allRowsQ c) (allRhsQ c) (allRowsQ_spec c) (allRhsQ_spec c)
      hsort₂ hlt₂ hlen₂).2 hfb₂
  have hall : ((List.range (c.rows + c.cols)).all fun k =>
      decide (k = 0) || decide (k ∈ List.range c.rows) ||
        decide (k ∈ (List.range c.cols).map (· + c.rows))) = true := by
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_range, List.mem_map]
    by_cases hkr : k < c.rows
    · exact .inl (.inr hkr)
    · exact .inr ⟨k - c.rows, by omega, by omega⟩
  simp only [isValidNodeExec, hwb, hvlen, length_zeroVertex, hT₁_eq, hT₂_eq, hlen₁, hlen₂, hall,
    hf1, hf2, decide_true, Bool.and_self]

private lemma validNode_props {c : BimatrixCode} (hc : c.WellFormed) {u : List Bool}
    (hu : isValidNodeExec c u = true) :
    u.length = 2 * (c.rows + c.cols) ∧
      (decodeT₁ c u).length = c.rows ∧ (decodeT₂ c u).length = c.cols ∧
      (∀ k : Fin c.rows ⊕ Fin c.cols, k ≠ .inl ⟨0, hc.1⟩ →
        k ∈ finsetOfList c.rows c.cols (decodeT₁ c u) ∨
          k ∈ finsetOfList c.rows c.cols (decodeT₂ c u)) ∧
      ∃ (h1 : (finsetOfList c.rows c.cols (decodeT₁ c u)).card = c.rows)
        (h2 : (finsetOfList c.rows c.cols (decodeT₂ c u)).card = c.cols),
        IsFeasibleBasis (intMatP (posMatB c))
          (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
          (finsetOfList c.rows c.cols (decodeT₁ c u)) h1 ∧
        IsFeasibleBasis (intMatQ (posMatA c))
          (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
          (finsetOfList c.rows c.cols (decodeT₂ c u)) h2 := by
  simp only [isValidNodeExec, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at hu
  rcases hu with ⟨⟨⟨⟨⟨⟨_, hlen_u⟩, hlen₁⟩, hlen₂⟩, hall⟩, hf1⟩, hf2⟩
  have hlt₁ : ∀ r ∈ decodeT₁ c u, r < c.rows + c.cols := fun _ hr => decodeT₁_lt c u hr
  have hlt₂ : ∀ r ∈ decodeT₂ c u, r < c.rows + c.cols := fun _ hr => decodeT₂_lt c u hr
  have hcard₁ : (finsetOfList c.rows c.cols (decodeT₁ c u)).card = c.rows :=
    (card_finsetOfList (decodeT₁_sorted c u).nodup hlt₁).trans hlen₁
  have hcard₂ : (finsetOfList c.rows c.cols (decodeT₂ c u)).card = c.cols :=
    (card_finsetOfList (decodeT₂_sorted c u).nodup hlt₂).trans hlen₂
  have hacl : ∀ k : Fin c.rows ⊕ Fin c.cols, k ≠ .inl ⟨0, hc.1⟩ →
      k ∈ finsetOfList c.rows c.cols (decodeT₁ c u) ∨
        k ∈ finsetOfList c.rows c.cols (decodeT₂ c u) := by
    intro k hk
    have hkne : (finSumFinEquiv k).1 ≠ 0 := by
      intro h0
      apply hk
      apply finSumFinEquiv.injective
      ext
      exact h0
    rcases hall (finSumFinEquiv k).1 (finSumFinEquiv k).2 with (h0 | h1) | h2
    · exact absurd h0 hkne
    · exact .inl (mem_finsetOfList.2 h1)
    · exact .inr (mem_finsetOfList.2 h2)
  have hfb₁ := (isFeasibleBasisRows_iff _ _ (allRowsP c) (allRhsP c) (allRowsP_spec c)
    (allRhsP_spec c) (decodeT₁_sorted c u) hlt₁ hlen₁).1 hf1
  have hfb₂ := (isFeasibleBasisRows_iff _ _ (allRowsQ c) (allRhsQ c) (allRowsQ_spec c)
    (allRhsQ_spec c) (decodeT₂_sorted c u) hlt₂ hlen₂).1 hf2
  exact ⟨hlen_u, hlen₁, hlen₂, hacl, hcard₁, hcard₂, hfb₁, hfb₂⟩

private lemma node_of_isValidNodeExec {c : BimatrixCode} (hc : c.WellFormed) {u : List Bool}
    (hu : isValidNodeExec c u = true) :
    ∃ (h1 : (finsetOfList c.rows c.cols (decodeT₁ c u)).card = c.rows)
      (h2 : (finsetOfList c.rows c.cols (decodeT₂ c u)).card = c.cols)
      (p : LemkeHowson.Node
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        (.inl ⟨0, hc.1⟩)),
      tightRows
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x =
        finsetOfList c.rows c.cols (decodeT₁ c u) ∧
      tightRows
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y =
        finsetOfList c.rows c.cols (decodeT₂ c u) ∧
      p.x = ratBasisSol (intMatP (posMatB c))
        (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (finsetOfList c.rows c.cols (decodeT₁ c u)) h1 ∧
      p.y = ratBasisSol (intMatQ (posMatA c))
        (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (finsetOfList c.rows c.cols (decodeT₂ c u)) h2 := by
  obtain ⟨_, _, _, hacl, hcard₁, hcard₂, hfb₁, hfb₂⟩ := validNode_props hc hu
  set x := ratBasisSol (intMatP (posMatB c))
    (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
    (finsetOfList c.rows c.cols (decodeT₁ c u)) hcard₁
  set y := ratBasisSol (intMatQ (posMatA c))
    (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
    (finsetOfList c.rows c.cols (decodeT₂ c u)) hcard₂
  have htx : tightRows
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) x =
      finsetOfList c.rows c.cols (decodeT₁ c u) :=
    tightRows_ratBasisSol_eq hfb₁ (pertP_nondegenerate hc)
  have hty : tightRows
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) y =
      finsetOfList c.rows c.cols (decodeT₂ c u) :=
    tightRows_ratBasisSol_eq hfb₂ (pertQ_nondegenerate hc)
  exact ⟨hcard₁, hcard₂,
    ⟨x, y, (isVertex_ratBasisSol_of_isFeasibleBasis hfb₁ (K := ℚ)).1,
      (isVertex_ratBasisSol_of_isFeasibleBasis hfb₂ (K := ℚ)).1,
      fun k hk => by rw [htx, hty]; exact hacl k hk⟩,
    htx, hty, rfl, rfl⟩

private lemma halfEdgeIndex_congr {m n : ℕ}
    (A₁ : Matrix (Fin m ⊕ Fin n) (Fin m) ℚ)
    (A₂ : Matrix (Fin m ⊕ Fin n) (Fin n) ℚ)
    {T₁ T₁' T₂ T₂' : Finset (Fin m ⊕ Fin n)}
    (hT₁ : T₁.card = m) (hT₁' : T₁'.card = m)
    (hT₂ : T₂.card = n) (hT₂' : T₂'.card = n)
    (h1 : T₁ = T₁') (h2 : T₂ = T₂') (k₀ : Fin m ⊕ Fin n) (side : Bool) :
    LemkeHowson.halfEdgeIndex A₁ A₂ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      T₁ T₂ hT₁ hT₂ k₀ side =
    LemkeHowson.halfEdgeIndex A₁ A₂ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      T₁' T₂' hT₁' hT₂' k₀ side := by
  subst h1 h2
  rfl

private lemma decodeT₁_encodeNodes_eq {c : BimatrixCode} {v : List Bool} {L₁ L₂ : List ℕ}
    (hv : v = encodeNodes c L₁ L₂) (hsort : L₁.Pairwise (· < ·))
    (hlt : ∀ k ∈ L₁, k < c.rows + c.cols) : decodeT₁ c v = L₁ := by
  refine (List.perm_of_nodup_nodup_toFinset_eq (decodeT₁_sorted c v).nodup
    hsort.nodup ?_).eq_of_pairwise
      (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2)) (decodeT₁_sorted c v) hsort
  ext k
  simp only [List.mem_toFinset]
  constructor
  · intro hk
    have hklt := decodeT₁_lt c v hk
    rw [hv] at hk
    exact (decodeT₁_encodeNodes L₁ L₂ hklt).1 hk
  · intro hk
    rw [hv]
    exact (decodeT₁_encodeNodes L₁ L₂ (hlt k hk)).2 hk

private lemma decodeT₂_encodeNodes_eq {c : BimatrixCode} {v : List Bool} {L₁ L₂ : List ℕ}
    (hv : v = encodeNodes c L₁ L₂) (hsort : L₂.Pairwise (· < ·))
    (hlt : ∀ k ∈ L₂, k < c.rows + c.cols) : decodeT₂ c v = L₂ := by
  refine (List.perm_of_nodup_nodup_toFinset_eq (decodeT₂_sorted c v).nodup
    hsort.nodup ?_).eq_of_pairwise
      (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2)) (decodeT₂_sorted c v) hsort
  ext k
  simp only [List.mem_toFinset]
  constructor
  · intro hk
    have hklt := decodeT₂_lt c v hk
    rw [hv] at hk
    exact (decodeT₂_encodeNodes L₁ L₂ hklt).1 hk
  · intro hk
    rw [hv]
    exact (decodeT₂_encodeNodes L₁ L₂ (hlt k hk)).2 hk

private lemma almostComplete_all_range_eq_true (m n : ℕ) (L₁ L₂ : List ℕ)
    {k₀ : Fin m ⊕ Fin n} (hk₀ : (finSumFinEquiv k₀).1 = 0)
    (hacl : ∀ k : Fin m ⊕ Fin n, k ≠ k₀ → k ∈ finsetOfList m n L₁ ∨ k ∈ finsetOfList m n L₂) :
    ((List.range (m + n)).all fun k =>
      decide (k = 0) || decide (k ∈ L₁) || decide (k ∈ L₂)) = true := by
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  by_cases hk0 : k = 0
  · exact .inl (.inl hk0)
  · have hk' : finSumFinEquiv.symm ⟨k, hk⟩ ≠ k₀ := fun h => by
      apply hk0
      have h1 := congrArg (fun z => (finSumFinEquiv z).1) h
      simp only [Equiv.apply_symm_apply] at h1
      exact h1.trans hk₀
    rcases hacl _ hk' with h1 | h2
    · exact .inl (.inr (by simpa [Equiv.apply_symm_apply] using mem_finsetOfList.1 h1))
    · exact .inr (by simpa [Equiv.apply_symm_apply] using mem_finsetOfList.1 h2)

private lemma stepGraph_roundTrip {c : BimatrixCode} (hc : c.WellFormed) (wantNeg : Bool)
    {u : List Bool} (hu : isValidNodeExec c u = true)
    (hact :
      (!decide (0 ∈ decodeT₂ c u) &&
        decide (halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) false =
          if wantNeg then -targetSign c else targetSign c)) = true ∨
      (!decide (0 ∈ decodeT₁ c u) &&
        decide (halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) true =
          if wantNeg then -targetSign c else targetSign c)) = true) :
    let v := stepGraph wantNeg c u
    isValidNodeExec c v = true ∧ v ≠ u ∧ stepGraph (!wantNeg) c v = u := by
  intro v
  have hwb : c.wellFormedB = true := (wellFormed_iff_wellFormedB c).1 hc
  have hsum_card : Fintype.card (Fin c.rows ⊕ Fin c.cols) = c.rows + c.cols := by simp
  obtain ⟨hcard₁, hcard₂, p, htx, hty, hpx_eq, hpy_eq⟩ := node_of_isValidNodeExec hc hu
  obtain ⟨hlen_u, hlen₁, hlen₂, hacl, _, _, hfb₁, hfb₂⟩ := validNode_props hc hu
  let T₁ := decodeT₁ c u
  let T₂ := decodeT₂ c u
  let T₁s := finsetOfList c.rows c.cols T₁
  let T₂s := finsetOfList c.rows c.cols T₂
  let k₀ : Fin c.rows ⊕ Fin c.cols := Sum.inl ⟨0, hc.1⟩
  let wanted := if wantNeg then -targetSign c else targetSign c
  let wanted' := if !wantNeg then -targetSign c else targetSign c
  have hw_opp : wanted' = -wanted := by cases wantNeg <;> simp [wanted, wanted']
  have hl_eq := leaveLabelExec_eq hc.1 (decodeT₁_sorted c u)
    (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr)
  let l' := LemkeHowson.leaveLabel T₁s T₂s k₀
  have hvalid_b : (!isValidNodeExec c u) = false := by simp [hu]
  by_cases hL : (!decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁ T₂ false = wanted)) = true
  · have hv_eq : v = encodeNodes c
        (pivotBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁
          (leaveLabelExec T₁ T₂)) T₂ := by
      dsimp only [v, stepGraph]
      rw [ite_eq_right (by simp [hvalid_b])]
      change (if (!decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁ T₂ false = wanted)) = true
          then _ else _) = _
      rw [ite_eq_left hL]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at hL
    obtain ⟨h0_not_T₂, hidxL⟩ := hL
    have hk₀_not_T₂s : k₀ ∉ T₂s := fun h => h0_not_T₂ (mem_finsetOfList.1 h)
    have hl'_in_T₁s : l' ∈ T₁s := by
      by_cases hk₀_in : k₀ ∈ T₁s
      · simp only [l', LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inl hk₀_in))]
        exact hk₀_in
      · exact (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard₁ hcard₂
          hacl (Finset.notMem_union.2 ⟨hk₀_in, hk₀_not_T₂s⟩)).1).1
    have hpiv := pivotBasisRows_spec (intMatP (posMatB c))
      (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
      (allRowsP c) (allRhsP c) (allRowsP_spec c) (allRhsP_spec c)
      (pertP_nondegenerate hc) (pertP_recession hc)
      (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr) hlen₁ hcard₁ hfb₁ hl'_in_T₁s
    dsimp only [T₁, T₂, T₁s, T₂s, l'] at hpiv
    rw [hl_eq, ← hpx_eq] at hpiv
    obtain ⟨hT₁'_sort, hT₁'_lt, hT₁'_len, hcard₁', hfb₁', hT₁'_tight⟩ := hpiv
    let T₁' := pivotBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁
      (leaveLabelExec T₁ T₂)
    let qx := pivotVertex
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x l'
    have hl'_in_px := Eq.mp (congrArg (l' ∈ ·) htx.symm) hl'_in_T₁s
    obtain ⟨hqx_v, hqx_ne, hqx_sub⟩ :=
      p.isVertex_x.pivotVertex_spec (pertP_nondegenerate hc) (pertP_recession hc) hl'_in_px
    have hT₁'_not_l' : l' ∉ finsetOfList c.rows c.cols T₁' := by
      rw [hT₁'_tight]
      exact p.isVertex_x.notMem_tightRows_pivotVertex (pertP_nondegenerate hc)
        (pertP_recession hc) hl'_in_px
    have hacl_q : ∀ k : Fin c.rows ⊕ Fin c.cols,
        k ≠ k₀ → k ∈ finsetOfList c.rows c.cols T₁' ∨ k ∈ T₂s := by
      intro k hk
      by_cases hkl : k = l'
      · subst hkl
        have hk₀_not_1 : k₀ ∉ T₁s := fun h => hk (by
          simp only [l', LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inl h))])
        exact .inr (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard₁ hcard₂
          hacl (Finset.notMem_union.2 ⟨hk₀_not_1, hk₀_not_T₂s⟩)).1).2
      · rcases hacl k hk with h1 | h2
        · refine .inl (hT₁'_tight ▸ hqx_sub (Finset.mem_erase.2 ⟨hkl, by rw [htx]; exact h1⟩))
        · exact .inr h2
    let q_node : LemkeHowson.Node
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) k₀ :=
      ⟨qx, p.y, hqx_v, p.isVertex_y, fun k hk => by
        rw [← hT₁'_tight, hty]
        exact hacl_q k hk⟩
    have hadj_pq : (LemkeHowson.graph
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) k₀).Adj
        p q_node := by
      rw [LemkeHowson.graph_adj]
      refine .inr ⟨rfl, ?_⟩
      exact (vertexAdj_iff_exists_pivotVertex (pertP_nondegenerate hc) (pertP_recession hc)
        p.isVertex_x).2 ⟨l', hl'_in_px, rfl⟩
    have hv_dec1 : decodeT₁ c v = T₁' := decodeT₁_encodeNodes_eq hv_eq hT₁'_sort hT₁'_lt
    have hv_dec2 : decodeT₂ c v = T₂ :=
      decodeT₂_encodeNodes_eq hv_eq (decodeT₂_sorted c u) (fun _ hr => decodeT₂_lt c u hr)
    have hv_valid : isValidNodeExec c v = true := by
      have hlen_v : v.length = 2 * (c.rows + c.cols) := by rw [hv_eq, length_encodeNodes]
      have hf1' : isFeasibleBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁' =
          true :=
        (isFeasibleBasisRows_iff _ _ (allRowsP c) (allRhsP c) (allRowsP_spec c) (allRhsP_spec c)
          hT₁'_sort hT₁'_lt hT₁'_len).2 hfb₁'
      have hf2' : isFeasibleBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂ =
          true :=
        (isFeasibleBasisRows_iff _ _ (allRowsQ c) (allRhsQ c) (allRowsQ_spec c) (allRhsQ_spec c)
          (decodeT₂_sorted c u) (fun _ hr => decodeT₂_lt c u hr) hlen₂).2 hfb₂
      have hall' : ((List.range (c.rows + c.cols)).all fun k =>
          decide (k = 0) || decide (k ∈ T₁') || decide (k ∈ T₂)) = true :=
        almostComplete_all_range_eq_true c.rows c.cols T₁' T₂ (by simp [k₀]) hacl_q
      have hlen₁' : T₁'.length = c.rows := hT₁'_len
      have hlen₂' : T₂.length = c.cols := hlen₂
      simp only [isValidNodeExec, hwb, hlen_v, hv_dec1, hv_dec2, hlen₁', hlen₂', hall', hf1', hf2',
        decide_true, Bool.and_self]
    have hv_ne : v ≠ u := by
      intro heq
      have hT_eq : T₁' = T₁ := by rw [← hv_dec1, heq]
      have hfin_eq : finsetOfList c.rows c.cols T₁' = T₁s :=
        congrArg (finsetOfList c.rows c.cols) hT_eq
      exact hT₁'_not_l' (hfin_eq.symm ▸ hl'_in_T₁s)
    have hidxL_v : halfEdgeIndexExec c T₁' T₂ false = wanted' := by
      have hexec_q := halfEdgeIndexExec_eq c hc.1 hT₁'_sort (decodeT₂_sorted c u) hT₁'_lt
        (fun _ hr => decodeT₂_lt c u hr) hT₁'_len hlen₂ false hacl_q hk₀_not_T₂s
      have hexec_p := halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) (decodeT₂_sorted c u)
        (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr) hlen₁ hlen₂ false
        hacl hk₀_not_T₂s
      have hpiv_idx := LemkeHowson.halfEdgeIndex_pivot_left_eq_neg (pertP_nondegenerate hc)
        (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Fintype.card_sum.trans (by simp))
        (p := p) (q := q_node) (hT₁p := by rw [htx]; exact hcard₁)
        (hT₁q := by rw [← hT₁'_tight]; exact hcard₁')
        (hT₂p := by rw [hty]; exact hcard₂) (hT₂q := by rw [hty]; exact hcard₂)
        rfl hqx_ne.symm hadj_pq
      have hp_congr := halfEdgeIndex_congr
        ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
        (by rw [htx]; exact hcard₁) hcard₁ (by rw [hty]; exact hcard₂) hcard₂
        htx hty k₀ false
      have hq_congr := halfEdgeIndex_congr
        ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
        (by rw [← hT₁'_tight]; exact hcard₁') hcard₁' (by rw [hty]; exact hcard₂) hcard₂
        hT₁'_tight.symm hty k₀ false
      rw [hexec_q, ← hq_congr]
      dsimp only [q_node] at hpiv_idx
      rw [hpiv_idx, hp_congr, ← hexec_p, hidxL, ← hw_opp]
    have hL_v :
        (!decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁' T₂ false = wanted')) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      exact ⟨h0_not_T₂, hidxL_v⟩
    have hv_step_back : stepGraph (!wantNeg) c v = u := by
      dsimp only [stepGraph]
      rw [ite_eq_right (by simp [hv_valid])]
      change (if (!decide (0 ∈ decodeT₂ c v) &&
          decide (halfEdgeIndexExec c (decodeT₁ c v) (decodeT₂ c v) false =
            if !wantNeg then -targetSign c else targetSign c)) = true
        then encodeNodes c (pivotBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c)
          (decodeT₁ c v) (leaveLabelExec (decodeT₁ c v) (decodeT₂ c v))) (decodeT₂ c v)
        else _) = _
      rw [hv_dec1, hv_dec2, ite_eq_left hL_v]
      let m'_fin := LemkeHowson.leaveLabel (finsetOfList c.rows c.cols T₁') T₂s k₀
      have hm'_eq_leave : (finSumFinEquiv m'_fin).1 = leaveLabelExec T₁' T₂ :=
        leaveLabelExec_eq hc.1 hT₁'_sort hT₁'_lt (fun _ hr => decodeT₂_lt c u hr)
      have hm'_in_T₁' : m'_fin ∈ finsetOfList c.rows c.cols T₁' := by
        by_cases hk₀_q : k₀ ∈ finsetOfList c.rows c.cols T₁'
        · simp only [m'_fin, LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inl hk₀_q))]
          exact hk₀_q
        · exact (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard₁' hcard₂
            hacl_q (Finset.notMem_union.2 ⟨hk₀_q, hk₀_not_T₂s⟩)).1).1
      have hqm'_eq_p : pivotVertex
          ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
          (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
          qx m'_fin = p.x := by
        symm
        refine hqx_v.eq_pivotVertex (pertP_nondegenerate hc) (pertP_recession hc)
          (by rw [← hT₁'_tight]; exact hm'_in_T₁') p.isVertex_x hqx_ne.symm ?_
        rw [← hT₁'_tight, htx]
        intro z hz
        rw [Finset.mem_erase] at hz
        have hnot_T₂ : z ∉ T₂s := by
          by_cases hzk₀ : z = k₀
          · exact hzk₀ ▸ hk₀_not_T₂s
          · intro hz2
            by_cases hk₀_q : k₀ ∈ finsetOfList c.rows c.cols T₁'
            · have he := LemkeHowson.inter_eq_empty_of_mem_union hsum_card hcard₁' hcard₂
                hacl_q (Finset.mem_union.2 (.inl hk₀_q))
              have hmem : z ∈ finsetOfList c.rows c.cols T₁' ∩ T₂s := Finset.mem_inter.2 ⟨hz.2, hz2⟩
              rw [he] at hmem
              exact Finset.notMem_empty z hmem
            · exact hz.1 (Finset.mem_singleton.1 ((LemkeHowson.mem_inter_of_acl_not_mem hsum_card
                hcard₁' hcard₂ hacl_q (Finset.notMem_union.2 ⟨hk₀_q, hk₀_not_T₂s⟩)).2 ▸
                Finset.mem_inter.2 ⟨hz.2, hz2⟩))
        have hzk₀ : z ≠ k₀ := by
          intro hzk
          have hk₀_q : k₀ ∈ finsetOfList c.rows c.cols T₁' ∪ T₂s :=
            Finset.mem_union.2 (.inl (hzk ▸ hz.2))
          have hm_eq : m'_fin = k₀ := by
            dsimp only [m'_fin]
            rw [LemkeHowson.leaveLabel, ite_eq_left hk₀_q]
          exact hz.1 (hzk.trans hm_eq.symm)
        exact (hacl z hzk₀).resolve_right hnot_T₂
      have hpiv_back := pivotBasisRows_spec (intMatP (posMatB c))
        (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (allRowsP c) (allRhsP c) (allRowsP_spec c) (allRhsP_spec c)
        (pertP_nondegenerate hc) (pertP_recession hc) hT₁'_sort hT₁'_lt hT₁'_len hcard₁' hfb₁'
        hm'_in_T₁'
      dsimp only [T₁, T₂, T₁s, T₂s] at hpiv_back
      have hrat_qx : ratBasisSol (intMatP (posMatB c))
          (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
          (finsetOfList c.rows c.cols T₁') hcard₁' = qx := by
        apply (isVertex_ratBasisSol_of_isFeasibleBasis hfb₁' (K := ℚ)).1.eq_of_tightRows_eq
        rw [tightRows_ratBasisSol_eq hfb₁' (pertP_nondegenerate hc), ← hT₁'_tight]
      rw [hrat_qx, hqm'_eq_p, hm'_eq_leave, htx] at hpiv_back
      obtain ⟨hT₁b_sort, hT₁b_lt, _, _, _, hT₁b_fin⟩ := hpiv_back
      have hT₁b_eq : pivotBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁'
          (leaveLabelExec T₁' T₂) = T₁ := by
        have hperm : (pivotBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁'
            (leaveLabelExec T₁' T₂)).Perm T₁ := by
          refine List.perm_of_nodup_nodup_toFinset_eq hT₁b_sort.nodup (decodeT₁_sorted c u).nodup ?_
          ext k
          simp only [List.mem_toFinset]
          by_cases hk : k < c.rows + c.cols
          · have hmem_eq : finsetOfList c.rows c.cols
                (pivotBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁'
                  (leaveLabelExec T₁' T₂)) = finsetOfList c.rows c.cols T₁ := hT₁b_fin
            have hiff := Finset.ext_iff.1 hmem_eq (finSumFinEquiv.symm ⟨k, hk⟩)
            simpa only [mem_finsetOfList, Equiv.apply_symm_apply] using hiff
          · exact ⟨fun h => absurd (hT₁b_lt k h) hk, fun h => absurd (decodeT₁_lt c u h) hk⟩
        exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2))
          hT₁b_sort (decodeT₁_sorted c u)
      rw [hT₁b_eq]
      exact encodeNodes_decode hlen_u
    exact ⟨hv_valid, hv_ne, hv_step_back⟩
  · have hR : (!decide (0 ∈ T₁) && decide (halfEdgeIndexExec c T₁ T₂ true = wanted)) = true :=
      hact.resolve_left hL
    have hv_eq : v = encodeNodes c T₁
        (pivotBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂
          (leaveLabelExec T₁ T₂)) := by
      dsimp only [v, stepGraph]
      rw [ite_eq_right (by simp [hvalid_b])]
      change (if (!decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁ T₂ false = wanted)) = true
          then _ else if (!decide (0 ∈ T₁) &&
            decide (halfEdgeIndexExec c T₁ T₂ true = wanted)) = true then _ else _) = _
      rw [ite_eq_right hL, ite_eq_left hR]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at hR
    obtain ⟨h0_not_T₁, hidxR⟩ := hR
    have hk₀_not_T₁s : k₀ ∉ T₁s := fun h => h0_not_T₁ (mem_finsetOfList.1 h)
    have hl'_in_T₂s : l' ∈ T₂s := by
      by_cases hk₀_in : k₀ ∈ T₂s
      · simp only [l', LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inr hk₀_in))]
        exact hk₀_in
      · exact (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard₁ hcard₂
          hacl (Finset.notMem_union.2 ⟨hk₀_not_T₁s, hk₀_in⟩)).1).2
    have hpiv := pivotBasisRows_spec (intMatQ (posMatA c))
      (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
      (allRowsQ c) (allRhsQ c) (allRowsQ_spec c) (allRhsQ_spec c)
      (pertQ_nondegenerate hc) (pertQ_recession hc)
      (decodeT₂_sorted c u) (fun _ hr => decodeT₂_lt c u hr) hlen₂ hcard₂ hfb₂ hl'_in_T₂s
    dsimp only [T₁, T₂, T₁s, T₂s, l'] at hpiv
    rw [hl_eq, ← hpy_eq] at hpiv
    obtain ⟨hT₂'_sort, hT₂'_lt, hT₂'_len, hcard₂', hfb₂', hT₂'_tight⟩ := hpiv
    let T₂' := pivotBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂
      (leaveLabelExec T₁ T₂)
    let qy := pivotVertex
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y l'
    have hl'_in_py := Eq.mp (congrArg (l' ∈ ·) hty.symm) hl'_in_T₂s
    obtain ⟨hqy_v, hqy_ne, hqy_sub⟩ :=
      p.isVertex_y.pivotVertex_spec (pertQ_nondegenerate hc) (pertQ_recession hc) hl'_in_py
    have hT₂'_not_l' : l' ∉ finsetOfList c.rows c.cols T₂' := by
      rw [hT₂'_tight]
      exact p.isVertex_y.notMem_tightRows_pivotVertex (pertQ_nondegenerate hc)
        (pertQ_recession hc) hl'_in_py
    have hacl_q : ∀ k : Fin c.rows ⊕ Fin c.cols,
        k ≠ k₀ → k ∈ T₁s ∨ k ∈ finsetOfList c.rows c.cols T₂' := by
      intro k hk
      by_cases hkl : k = l'
      · subst hkl
        have hk₀_not_2 : k₀ ∉ T₂s := fun h => hk (by
          simp only [l', LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inr h))])
        exact .inl (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard₁ hcard₂
          hacl (Finset.notMem_union.2 ⟨hk₀_not_T₁s, hk₀_not_2⟩)).1).1
      · rcases hacl k hk with h1 | h2
        · exact .inl h1
        · refine .inr (hT₂'_tight ▸ hqy_sub (Finset.mem_erase.2 ⟨hkl, by rw [hty]; exact h2⟩))
    let q_node : LemkeHowson.Node
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) k₀ :=
      ⟨p.x, qy, p.isVertex_x, hqy_v, fun k hk => by
        rw [htx, ← hT₂'_tight]
        exact hacl_q k hk⟩
    have hadj_pq : (LemkeHowson.graph
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) k₀).Adj
        p q_node := by
      rw [LemkeHowson.graph_adj]
      refine .inl ⟨rfl, ?_⟩
      exact (vertexAdj_iff_exists_pivotVertex (pertQ_nondegenerate hc) (pertQ_recession hc)
        p.isVertex_y).2 ⟨l', hl'_in_py, rfl⟩
    have hv_dec1 : decodeT₁ c v = T₁ :=
      decodeT₁_encodeNodes_eq hv_eq (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr)
    have hv_dec2 : decodeT₂ c v = T₂' := decodeT₂_encodeNodes_eq hv_eq hT₂'_sort hT₂'_lt
    have hv_valid : isValidNodeExec c v = true := by
      have hlen_v : v.length = 2 * (c.rows + c.cols) := by rw [hv_eq, length_encodeNodes]
      have hf1' : isFeasibleBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁ =
          true :=
        (isFeasibleBasisRows_iff _ _ (allRowsP c) (allRhsP c) (allRowsP_spec c) (allRhsP_spec c)
          (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr) hlen₁).2 hfb₁
      have hf2' : isFeasibleBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂' =
          true :=
        (isFeasibleBasisRows_iff _ _ (allRowsQ c) (allRhsQ c) (allRowsQ_spec c) (allRhsQ_spec c)
          hT₂'_sort hT₂'_lt hT₂'_len).2 hfb₂'
      have hall' : ((List.range (c.rows + c.cols)).all fun k =>
          decide (k = 0) || decide (k ∈ T₁) || decide (k ∈ T₂')) = true :=
        almostComplete_all_range_eq_true c.rows c.cols T₁ T₂' (by simp [k₀]) hacl_q
      have hlen₁' : T₁.length = c.rows := hlen₁
      have hlen₂' : T₂'.length = c.cols := hT₂'_len
      simp only [isValidNodeExec, hwb, hlen_v, hv_dec1, hv_dec2, hlen₁', hlen₂', hall', hf1', hf2',
        decide_true, Bool.and_self]
    have hv_ne : v ≠ u := by
      intro heq
      have hT_eq : T₂' = T₂ := by rw [← hv_dec2, heq]
      have hfin_eq : finsetOfList c.rows c.cols T₂' = T₂s :=
        congrArg (finsetOfList c.rows c.cols) hT_eq
      exact hT₂'_not_l' (hfin_eq.symm ▸ hl'_in_T₂s)
    have hidxR_v : halfEdgeIndexExec c T₁ T₂' true = wanted' := by
      have hexec_q := halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) hT₂'_sort
        (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt hlen₁ hT₂'_len true hacl_q hk₀_not_T₁s
      have hexec_p := halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) (decodeT₂_sorted c u)
        (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr) hlen₁ hlen₂ true
        hacl hk₀_not_T₁s
      have hpiv_idx := LemkeHowson.halfEdgeIndex_pivot_right_eq_neg (pertQ_nondegenerate hc)
        (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) hsum_card
        (p := p) (q := q_node) (hT₁p := by rw [htx]; exact hcard₁)
        (hT₁q := by rw [htx]; exact hcard₁)
        (hT₂p := by rw [hty]; exact hcard₂) (hT₂q := by rw [← hT₂'_tight]; exact hcard₂')
        rfl hqy_ne.symm hadj_pq
      have hp_congr := halfEdgeIndex_congr
        ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
        (by rw [htx]; exact hcard₁) hcard₁ (by rw [hty]; exact hcard₂) hcard₂
        htx hty k₀ true
      have hq_congr := halfEdgeIndex_congr
        ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
        (by rw [htx]; exact hcard₁) hcard₁ (by rw [← hT₂'_tight]; exact hcard₂') hcard₂'
        htx hT₂'_tight.symm k₀ true
      rw [hexec_q, ← hq_congr]
      dsimp only [q_node] at hpiv_idx
      rw [hpiv_idx, hp_congr, ← hexec_p, hidxR, ← hw_opp]
    have hL_v_false :
        (!decide (0 ∈ T₂') && decide (halfEdgeIndexExec c T₁ T₂' false = wanted')) = false := by
      by_cases h02' : 0 ∈ T₂'
      · simp [h02']
      · simp only [Bool.and_eq_false_imp, Bool.not_eq_true', decide_eq_false_iff_not]
        intro _ heq_f
        have h0_T₂' : k₀ ∉ finsetOfList c.rows c.cols T₂' := fun h => h02' (mem_finsetOfList.1 h)
        have hneq_half := LemkeHowson.halfEdgeIndex_true_eq_neg_false
          (A₁ := ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ))
          (A₂ := ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ))
          (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) hsum_card
          q_node (hT₁ := by rw [htx]; exact hcard₁) (hT₂ := by rw [← hT₂'_tight]; exact hcard₂')
          (fun hcl => by
            rw [LemkeHowson.completelyLabeled_iff] at hcl
            rcases hcl k₀ with h1 | h2
            · dsimp only [q_node] at h1
              rw [htx] at h1
              exact hk₀_not_T₁s h1
            · exact h0_T₂' (by rw [hT₂'_tight]; exact h2))
        have hne_0 := LemkeHowson.halfEdgeIndex_ne_zero
          (A₁ := ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ))
          (A₂ := ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ))
          (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) hsum_card
          q_node (hT₁ := by rw [htx]; exact hcard₁) (hT₂ := by rw [← hT₂'_tight]; exact hcard₂')
          (side := false) (fun h => h0_T₂' (by rw [hT₂'_tight]; exact h))
        have hcongr := halfEdgeIndex_congr
          ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
          ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
          (by rw [htx]; exact hcard₁) hcard₁ (by rw [← hT₂'_tight]; exact hcard₂') hcard₂'
          htx hT₂'_tight.symm k₀
        have h1 : halfEdgeIndexExec c T₁ T₂' true = -halfEdgeIndexExec c T₁ T₂' false := by
          rw [halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) hT₂'_sort
              (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt hlen₁ hT₂'_len true hacl_q hk₀_not_T₁s,
            halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) hT₂'_sort
              (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt hlen₁ hT₂'_len false hacl_q h0_T₂',
            ← hcongr true, ← hcongr false]
          exact hneq_half
        rw [hidxR_v, heq_f] at h1
        have hw0 : wanted' = 0 := by omega
        have h0_eq : halfEdgeIndexExec c T₁ T₂' false = 0 := heq_f.trans hw0
        rw [halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) hT₂'_sort
            (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt hlen₁ hT₂'_len false hacl_q h0_T₂',
          ← hcongr false] at h0_eq
        exact hne_0 h0_eq
    have hR_v :
        (!decide (0 ∈ T₁) && decide (halfEdgeIndexExec c T₁ T₂' true = wanted')) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      exact ⟨h0_not_T₁, hidxR_v⟩
    have hv_step_back : stepGraph (!wantNeg) c v = u := by
      dsimp only [stepGraph]
      rw [ite_eq_right (by simp [hv_valid])]
      change (if (!decide (0 ∈ decodeT₂ c v) &&
          decide (halfEdgeIndexExec c (decodeT₁ c v) (decodeT₂ c v) false =
            if !wantNeg then -targetSign c else targetSign c)) = true
        then _ else
        if (!decide (0 ∈ decodeT₁ c v) &&
          decide (halfEdgeIndexExec c (decodeT₁ c v) (decodeT₂ c v) true =
            if !wantNeg then -targetSign c else targetSign c)) = true
        then encodeNodes c (decodeT₁ c v)
          (pivotBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c)
            (decodeT₂ c v) (leaveLabelExec (decodeT₁ c v) (decodeT₂ c v)))
        else _) = _
      rw [hv_dec1, hv_dec2, ite_eq_right (Bool.eq_false_iff.1 hL_v_false), ite_eq_left hR_v]
      let m'_fin := LemkeHowson.leaveLabel T₁s (finsetOfList c.rows c.cols T₂') k₀
      have hm'_eq_leave : (finSumFinEquiv m'_fin).1 = leaveLabelExec T₁ T₂' :=
        leaveLabelExec_eq hc.1 (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt
      have hm'_in_T₂' : m'_fin ∈ finsetOfList c.rows c.cols T₂' := by
        by_cases hk₀_q : k₀ ∈ finsetOfList c.rows c.cols T₂'
        · simp only [m'_fin, LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inr hk₀_q))]
          exact hk₀_q
        · exact (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard₁ hcard₂'
            hacl_q (Finset.notMem_union.2 ⟨hk₀_not_T₁s, hk₀_q⟩)).1).2
      have hqm'_eq_p : pivotVertex
          ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
          (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
          qy m'_fin = p.y := by
        symm
        refine hqy_v.eq_pivotVertex (pertQ_nondegenerate hc) (pertQ_recession hc)
          (by rw [← hT₂'_tight]; exact hm'_in_T₂') p.isVertex_y hqy_ne.symm ?_
        rw [← hT₂'_tight, hty]
        intro z hz
        rw [Finset.mem_erase] at hz
        have hnot_T₁ : z ∉ T₁s := by
          by_cases hzk₀ : z = k₀
          · exact hzk₀ ▸ hk₀_not_T₁s
          · intro hz1
            by_cases hk₀_q : k₀ ∈ finsetOfList c.rows c.cols T₂'
            · have he := LemkeHowson.inter_eq_empty_of_mem_union hsum_card hcard₁ hcard₂'
                hacl_q (Finset.mem_union.2 (.inr hk₀_q))
              have hmem : z ∈ T₁s ∩ finsetOfList c.rows c.cols T₂' := Finset.mem_inter.2 ⟨hz1, hz.2⟩
              rw [he] at hmem
              exact Finset.notMem_empty z hmem
            · exact hz.1 (Finset.mem_singleton.1 ((LemkeHowson.mem_inter_of_acl_not_mem hsum_card
                hcard₁ hcard₂' hacl_q (Finset.notMem_union.2 ⟨hk₀_not_T₁s, hk₀_q⟩)).2 ▸
                Finset.mem_inter.2 ⟨hz1, hz.2⟩))
        have hzk₀ : z ≠ k₀ := by
          intro hzk
          have hk₀_q : k₀ ∈ T₁s ∪ finsetOfList c.rows c.cols T₂' :=
            Finset.mem_union.2 (.inr (hzk ▸ hz.2))
          have hm_eq : m'_fin = k₀ := by
            dsimp only [m'_fin]
            rw [LemkeHowson.leaveLabel, ite_eq_left hk₀_q]
          exact hz.1 (hzk.trans hm_eq.symm)
        exact (hacl z hzk₀).resolve_left hnot_T₁
      have hpiv_back := pivotBasisRows_spec (intMatQ (posMatA c))
        (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (allRowsQ c) (allRhsQ c) (allRowsQ_spec c) (allRhsQ_spec c)
        (pertQ_nondegenerate hc) (pertQ_recession hc) hT₂'_sort hT₂'_lt hT₂'_len hcard₂' hfb₂'
        hm'_in_T₂'
      dsimp only [T₁, T₂, T₁s, T₂s] at hpiv_back
      have hrat_qy : ratBasisSol (intMatQ (posMatA c))
          (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
          (finsetOfList c.rows c.cols T₂') hcard₂' = qy := by
        apply (isVertex_ratBasisSol_of_isFeasibleBasis hfb₂' (K := ℚ)).1.eq_of_tightRows_eq
        rw [tightRows_ratBasisSol_eq hfb₂' (pertQ_nondegenerate hc), ← hT₂'_tight]
      rw [hrat_qy, hqm'_eq_p, hm'_eq_leave, hty] at hpiv_back
      obtain ⟨hT₂b_sort, hT₂b_lt, _, _, _, hT₂b_fin⟩ := hpiv_back
      have hT₂b_eq : pivotBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂'
          (leaveLabelExec T₁ T₂') = T₂ := by
        have hperm : (pivotBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂'
            (leaveLabelExec T₁ T₂')).Perm T₂ := by
          refine List.perm_of_nodup_nodup_toFinset_eq hT₂b_sort.nodup (decodeT₂_sorted c u).nodup ?_
          ext k
          simp only [List.mem_toFinset]
          by_cases hk : k < c.rows + c.cols
          · have hmem_eq : finsetOfList c.rows c.cols
                (pivotBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂'
                  (leaveLabelExec T₁ T₂')) = finsetOfList c.rows c.cols T₂ := hT₂b_fin
            have hiff := Finset.ext_iff.1 hmem_eq (finSumFinEquiv.symm ⟨k, hk⟩)
            simpa only [mem_finsetOfList, Equiv.apply_symm_apply] using hiff
          · exact ⟨fun h => absurd (hT₂b_lt k h) hk, fun h => absurd (decodeT₂_lt c u h) hk⟩
        exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2))
          hT₂b_sort (decodeT₂_sorted c u)
      rw [hT₂b_eq]
      exact encodeNodes_decode hlen_u
    exact ⟨hv_valid, hv_ne, hv_step_back⟩

private lemma endOfLineRel_wellFormed_props {c : BimatrixCode} (hc : c.WellFormed) {u : List Bool}
    (hu : endOfLineRel vertexLen pred succ c u) :
    isValidNodeExec c u = true ∧ u ≠ zeroVertex (vertexLen c) ∧
      (0 ∈ decodeT₁ c u ∨ 0 ∈ decodeT₂ c u) := by
  have hwb : c.wellFormedB = true := (wellFormed_iff_wellFormedB c).1 hc
  have hvlen : vertexLen c = 2 * (c.rows + c.cols) := by simp [vertexLen, hwb]
  have hvalid_zero := isValidNodeExec_zeroVertex hc
  have hu_valid : isValidNodeExec c u = true := by
    by_contra hnot
    have hnot' : (!isValidNodeExec c u) = true := by cases h : isValidNodeExec c u <;> simp_all
    have hp : pred (c, u) = u := by
      dsimp only [pred, stepGraph]
      rw [ite_eq_left hnot']
    have hs : succ (c, u) = u := by
      dsimp only [succ, stepGraph]
      rw [ite_eq_left hnot']
    have hin : hasIn vertexLen pred succ c u = false := by simp [hasIn, hp]
    have hout : hasOut vertexLen pred succ c u = false := by simp [hasOut, hs]
    have hne : u ≠ zeroVertex (vertexLen c) := fun h => hnot (h ▸ hvalid_zero)
    rcases hu with ⟨-, hrel⟩
    simp [hin, hout, hne] at hrel
  set u0 := zeroVertex (vertexLen c)
  have hT₁_eq0 : decodeT₁ c u0 = List.range c.rows := by
    dsimp only [u0]; rw [hvlen, decodeT₁_zeroVertex]
  have hT₂_eq0 : decodeT₂ c u0 = (List.range c.cols).map (· + c.rows) := by
    dsimp only [u0]; rw [hvlen, decodeT₂_zeroVertex]
  have h01_0 : 0 ∈ decodeT₁ c u0 := by rw [hT₁_eq0, List.mem_range]; exact hc.1
  have h02_0 : 0 ∉ decodeT₂ c u0 := by
    rw [hT₂_eq0, List.mem_map]
    rintro ⟨j, _, hj⟩
    have := hc.1
    omega
  have hidx0 : halfEdgeIndexExec c (decodeT₁ c u0) (decodeT₂ c u0) false = targetSign c := by
    obtain ⟨_, hlen₁, hlen₂, hacl, _, _, _, _⟩ := validNode_props hc hvalid_zero
    have hT₁_fin : finsetOfList c.rows c.cols (decodeT₁ c u0) = Finset.univ.image Sum.inl := by
      rw [hT₁_eq0]
      ext r
      simp only [mem_finsetOfList, List.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
      cases r with
      | inl i => exact ⟨fun _ => ⟨i, rfl⟩, fun _ => i.2⟩
      | inr j =>
        refine ⟨fun h => ?_, fun ⟨i, hi⟩ => absurd hi (by simp)⟩
        simp only [finSumFinEquiv_apply_right, Fin.val_natAdd] at h
        omega
    have hT₂_fin : finsetOfList c.rows c.cols (decodeT₂ c u0) = Finset.univ.image Sum.inr := by
      rw [hT₂_eq0]
      ext r
      simp only [mem_finsetOfList, List.mem_map, List.mem_range, Finset.mem_image, Finset.mem_univ,
        true_and]
      cases r with
      | inl i =>
        refine ⟨?_, fun ⟨j, hj⟩ => absurd hj (by simp)⟩
        rintro ⟨j, _, hj⟩
        simp only [finSumFinEquiv_apply_left, Fin.val_castAdd] at hj
        omega
      | inr j => exact ⟨fun _ => ⟨j, rfl⟩, fun _ => ⟨j.1, j.2, by simp [Nat.add_comm]⟩⟩
    have hA₁_neg :
        ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ).submatrix
          ((Equiv.refl (Fin c.rows ⊕ Fin c.cols)) ∘ Sum.inl) (Equiv.refl _) = -1 := by
      ext i j
      simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.refl_apply, Matrix.map_apply,
        intMatP_inl, Matrix.neg_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hA₂_neg :
        ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ).submatrix
          ((Equiv.refl (Fin c.rows ⊕ Fin c.cols)) ∘ Sum.inr) (Equiv.refl _) = -1 := by
      ext i j
      simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.refl_apply, Matrix.map_apply,
        intMatQ_inr, Matrix.neg_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u0) (decodeT₂_sorted c u0)
        (fun _ hr => decodeT₁_lt c u0 hr) (fun _ hr => decodeT₂_lt c u0 hr) hlen₁ hlen₂ false
        hacl (fun h => h02_0 (mem_finsetOfList.1 h)),
      LemkeHowson.halfEdgeIndex_zero_zero _ _ _ _ _ _ _ hT₁_fin hT₂_fin hA₁_neg hA₂_neg,
      ← targetSign_eq]
  have hpred0 : pred (c, u0) = u0 := by
    have hnotv : (!isValidNodeExec c u0) = false := by
      simp only [hvalid_zero, Bool.not_true]
    have hne_neg : halfEdgeIndexExec c (decodeT₁ c u0) (decodeT₂ c u0) false ≠ -targetSign c := by
      rw [hidx0]
      have hts := targetSign_eq c
      rcases neg_one_pow_eq_or ℤ (c.rows + c.cols) with h | h <;> rw [h] at hts <;> omega
    have hcond1 : (!decide (0 ∈ decodeT₂ c u0) &&
        decide (halfEdgeIndexExec c (decodeT₁ c u0) (decodeT₂ c u0) false = -targetSign c)) =
        false := by
      simp [hne_neg]
    have hcond2 : (!decide (0 ∈ decodeT₁ c u0) &&
        decide (halfEdgeIndexExec c (decodeT₁ c u0) (decodeT₂ c u0) true = -targetSign c)) =
        false := by
      simp [h01_0]
    dsimp only [pred, stepGraph]
    simp only [hnotv, Bool.false_eq_true, ↓reduceIte, hcond1, hcond2]
  have hu_ne_zero : u ≠ u0 := by
    intro h0
    subst h0
    have hrt := stepGraph_roundTrip hc false hvalid_zero (.inl (by simp [h02_0, hidx0]))
    have hout : hasOut vertexLen pred succ c u0 = true := by
      simp only [hasOut, decide_eq_true_eq]
      exact ⟨hrt.2.2, hrt.2.1, hrt.2.1⟩
    rcases hu with ⟨-, hrel⟩
    simp [u0, hout] at hrel
  have hcl : 0 ∈ decodeT₁ c u ∨ 0 ∈ decodeT₂ c u := by
    by_contra hnot
    push Not at hnot
    obtain ⟨h01, h02⟩ := hnot
    obtain ⟨_, hlen₁, hlen₂, hacl, hcard₁, hcard₂, _, _⟩ := validNode_props hc hu_valid
    obtain ⟨_, _, p, htx, hty, _, _⟩ := node_of_isValidNodeExec hc hu_valid
    let k₀ : Fin c.rows ⊕ Fin c.cols := Sum.inl ⟨0, hc.1⟩
    have hk₀1 : k₀ ∉ finsetOfList c.rows c.cols (decodeT₁ c u) :=
      fun h => h01 (mem_finsetOfList.1 h)
    have hk₀2 : k₀ ∉ finsetOfList c.rows c.cols (decodeT₂ c u) :=
      fun h => h02 (mem_finsetOfList.1 h)
    have hidx_opp : halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) true =
        -halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) false := by
      rw [halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) (decodeT₂_sorted c u)
          (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr)
          hlen₁ hlen₂ true hacl hk₀1,
        halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) (decodeT₂_sorted c u)
          (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr)
          hlen₁ hlen₂ false hacl hk₀2]
      have hhe := LemkeHowson.halfEdgeIndex_true_eq_neg_false
        (A₁ := ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ))
        (A₂ := ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ))
        (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Fintype.card_sum.trans (by simp)) p
        (hT₁ := by rw [htx]; exact hcard₁) (hT₂ := by rw [hty]; exact hcard₂)
        (fun hcl => by
          rw [LemkeHowson.completelyLabeled_iff] at hcl
          rcases hcl k₀ with h1 | h2
          · exact hk₀1 (htx ▸ h1)
          · exact hk₀2 (hty ▸ h2))
      have hcongr := halfEdgeIndex_congr
        ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
        (by rw [htx]; exact hcard₁) hcard₁ (by rw [hty]; exact hcard₂) hcard₂
        htx hty k₀
      rw [← hcongr true, ← hcongr false]
      exact hhe
    have hidx_sq : (halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) false = targetSign c) ∨
        (halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) false = -targetSign c) := by
      have hne0 := LemkeHowson.halfEdgeIndex_ne_zero
        (A₁ := ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ))
        (A₂ := ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ))
        (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Fintype.card_sum.trans (by simp)) p
        (hT₁ := by rw [htx]; exact hcard₁) (hT₂ := by rw [hty]; exact hcard₂)
        (side := false) (fun h => hk₀2 (hty ▸ h))
      have hs1 : ∀ u : ℤˣ, |(u : ℤ)| ≤ 1 := fun u => by
        rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
      have hs2 : ∀ x : ℚ, |LemkeHowson.signOfK x| ≤ 1 := fun x => by
        simp only [LemkeHowson.signOfK]
        cases SignType.sign x <;> norm_num
      have hle_abs : |LemkeHowson.halfEdgeIndex
          ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
          ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
          (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
          (tightRows ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
            (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x)
          (tightRows ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
            (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y)
          (by rw [htx]; exact hcard₁) (by rw [hty]; exact hcard₂) k₀ false| ≤ 1 := by
        simp only [LemkeHowson.halfEdgeIndex]
        split_ifs
        · rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul (hs1 _) (hs2 _) (abs_nonneg _) (by norm_num))
            (hs2 _) (abs_nonneg _) (by norm_num)
        · norm_num
      have hcongr := halfEdgeIndex_congr
        ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
        (by rw [htx]; exact hcard₁) hcard₁ (by rw [hty]; exact hcard₂) hcard₂
        htx hty k₀ false
      have habs1 : |halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) false| = 1 := by
        rw [halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u) (decodeT₂_sorted c u)
            (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr)
            hlen₁ hlen₂ false hacl hk₀2, ← hcongr]
        have hpos : 0 < |LemkeHowson.halfEdgeIndex
            ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
            ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
            (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
            (tightRows ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
              (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x)
            (tightRows ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
              (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y)
            (by rw [htx]; exact hcard₁) (by rw [hty]; exact hcard₂) k₀ false| := abs_pos.2 hne0
        omega
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at habs1
      have hts := targetSign_eq c
      rcases neg_one_pow_eq_or ℤ (c.rows + c.cols) with hts1 | hts1 <;> rw [hts1] at hts <;>
        rcases habs1 with h1 | h1 <;> [exact .inl (by omega); exact .inr (by omega);
          exact .inr (by omega); exact .inl (by omega)]
    have hout : hasOut vertexLen pred succ c u = true := by
      rcases hidx_sq with hpos | hneg
      · have hrt := stepGraph_roundTrip hc false hu_valid (.inl (by simp [h02, hpos]))
        have hne0 : succ (c, u) ≠ u0 := fun h0 => by
          have hpb : u = pred (c, u0) := h0 ▸ hrt.2.2.symm
          exact hu_ne_zero (hpb.trans hpred0)
        simp only [hasOut, decide_eq_true_eq]
        exact ⟨hrt.2.2, hrt.2.1, hne0⟩
      · have hposR : halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) true = targetSign c := by
          rw [hidx_opp, hneg, neg_neg]
        have hrt := stepGraph_roundTrip hc false hu_valid (.inr (by simp [h01, hposR]))
        have hne0 : succ (c, u) ≠ u0 := fun h0 => by
          have hpb : u = pred (c, u0) := h0 ▸ hrt.2.2.symm
          exact hu_ne_zero (hpb.trans hpred0)
        simp only [hasOut, decide_eq_true_eq]
        exact ⟨hrt.2.2, hrt.2.1, hne0⟩
    have hin : hasIn vertexLen pred succ c u = true := by
      rcases hidx_sq with hpos | hneg
      · have hnegR : halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) true = -targetSign c := by
          rw [hidx_opp, hpos]
        have hrt := stepGraph_roundTrip hc true hu_valid (.inr (by simp [h01, hnegR]))
        simp only [hasIn, decide_eq_true_eq]
        exact ⟨hrt.2.2, hrt.2.1, hu_ne_zero⟩
      · have hrt := stepGraph_roundTrip hc true hu_valid (.inl (by simp [h02, hneg]))
        simp only [hasIn, decide_eq_true_eq]
        exact ⟨hrt.2.2, hrt.2.1, hu_ne_zero⟩
    rcases hu with ⟨-, hrel⟩
    have hu_ne' : u ≠ zeroVertex (vertexLen c) := hu_ne_zero
    simp [hin, hout, hu_ne'] at hrel
  exact ⟨hu_valid, hu_ne_zero, hcl⟩

/-! ### Section 6: Witness extraction and `PPAD` membership -/

/-- Reduce a nonnegative rational represented by `(num, den)` (`0 ≤ num`, `0 < den`) to canonical
lowest-terms representation `(num / gcd, den / gcd)`. -/
private def reduceIntPair (num den : ℤ) : ℤ × ℕ :=
  let g := Nat.gcd num.natAbs den.natAbs
  (((num.natAbs / g : ℕ) : ℤ), den.natAbs / g)

private theorem reduceIntPair_polytime {α : Type} {encIn : α ↪ List Bool}
    {num den : α → ℤ}
    (hnum : ComputableInPolyTime num encIn encIntBin)
    (hden : ComputableInPolyTime den encIn encIntBin) :
    ComputableInPolyTime (fun x => reduceIntPair (num x) (den x)) encIn encRatData := by
  have ha := intBin_natAbs.comp hnum
  have hb := intBin_natAbs.comp hden
  have hg := binary_gcd' ha hb
  have hq1 := intBin_natCast.comp (binary_div' ha hg)
  have hq2 := binary_div' hb hg
  exact (hq1.prod hq2).of_enc_eq fun _ => rfl

private lemma reduceIntPair_spec {num den : ℤ} (hnum : 0 ≤ num) (hden : 0 < den) :
    isCanonicalNonnegPair (reduceIntPair num den) = true ∧
      mkRatOfPair (reduceIntPair num den) = (num : ℚ) / (den : ℚ) := by
  dsimp only [reduceIntPair]
  set g := Nat.gcd num.natAbs den.natAbs
  have hden_pos : 0 < den.natAbs := Int.natAbs_pos.2 hden.ne'
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right _ hden_pos
  have hdiv_pos : 0 < den.natAbs / g :=
    Nat.div_pos (Nat.le_of_dvd hden_pos (Nat.gcd_dvd_right _ _)) hg_pos
  have hcop : Nat.gcd (num.natAbs / g) (den.natAbs / g) = 1 :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right hden_pos
  refine ⟨?_, ?_⟩
  · simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq, Int.natAbs_natCast]
    exact ⟨⟨Int.natCast_nonneg _, hdiv_pos⟩, hcop⟩
  · have hnum_eq : ((num.natAbs : ℕ) : ℤ) = num := Int.natAbs_of_nonneg hnum
    have hden_eq : ((den.natAbs : ℕ) : ℤ) = den := Int.natAbs_of_nonneg hden.le
    have h1 : (((num.natAbs / g : ℕ) * g : ℕ) : ℤ) = num := by
      rw [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), hnum_eq]
    have h2 : (((den.natAbs / g : ℕ) * g : ℕ) : ℤ) = den := by
      rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), hden_eq]
    have hmul1Q : (((num.natAbs / g : ℕ) : ℤ) : ℚ) * (g : ℚ) = (num : ℚ) := by
      rw [Int.cast_natCast, ← Nat.cast_mul]
      simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℚ) h1
    have hmul2Q : ((den.natAbs / g : ℕ) : ℚ) * (g : ℚ) = (den : ℚ) := by
      rw [← Nat.cast_mul]
      simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℚ) h2
    have hgQ : (g : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hg_pos.ne'
    have hdenQ : (den : ℚ) ≠ 0 := Int.cast_ne_zero.2 hden.ne'
    have hdivQ : ((den.natAbs / g : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hdiv_pos.ne'
    dsimp only [mkRatOfPair]
    rw [div_eq_div_iff hdivQ hdenQ, ← mul_left_inj' hgQ]
    calc (((num.natAbs / g : ℕ) : ℤ) : ℚ) * (den : ℚ) * (g : ℚ)
        = ((((num.natAbs / g : ℕ) : ℤ) : ℚ) * (g : ℚ)) * (den : ℚ) := by ring
      _ = (num : ℚ) * (den : ℚ) := by rw [hmul1Q]
      _ = (num : ℚ) * (((den.natAbs / g : ℕ) : ℚ) * (g : ℚ)) := by rw [hmul2Q]
      _ = (num : ℚ) * ((den.natAbs / g : ℕ) : ℚ) * (g : ℚ) := by ring

/-- Sign-adjusted unperturbed Cramer numerator vector `det(M_T).sign • cramerVec(M_T, b|_T)`
computed from row lists without division. -/
private def extractStrategyNum (k : ℕ) (allRows : List (List ℤ)) (allRhs : List ℤ)
    (T : List ℕ) : List ℤ :=
  let M := subRows k allRows T
  let s := (detRows M).sign
  (cramerVecRows k M (subRhs allRhs T)).map fun x => s * x

/-- Normalize a list of nonnegative integer weights by their sum into lowest-terms pairs. -/
private def normalizeRatPairs (nums : List ℤ) : List (ℤ × ℕ) :=
  let S := nums.sum
  nums.map fun num => reduceIntPair num S

private theorem extractStrategyNum_polytime {α : Type} {encIn : α ↪ List Bool}
    {k : α → ℕ} {allRows : α → List (List ℤ)} {allRhs : α → List ℤ} {T : α → List ℕ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hall : ComputableInPolyTime allRows encIn encIntTable)
    (hrhs : ComputableInPolyTime allRhs encIn (encList encIntBin))
    (hT : ComputableInPolyTime T encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => extractStrategyNum (k x) (allRows x) (allRhs x) (T x))
      encIn (encList encIntBin) := by
  have hM := subRows_polytime hk hall hT
  have hs := intBin_sign.comp (detRows_polytime.comp hM)
  have hcv := cramerVecRows_polytime hk hM (subRhs_polytime hrhs hT)
  unfold extractStrategyNum
  refine mapWithInput (encA := encIntBin) hcv ?_
  exact intBin_mul' (hs.comp (fst encIn encIntBin)) (snd encIn encIntBin)

private theorem normalizeRatPairs_polytime {α : Type} {encIn : α ↪ List Bool}
    {nums : α → List ℤ} (hnums : ComputableInPolyTime nums encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => normalizeRatPairs (nums x)) encIn (encList encRatData) := by
  have hS := intBin_sum.comp hnums
  unfold normalizeRatPairs
  refine mapWithInput (encA := encIntBin) hnums ?_
  exact reduceIntPair_polytime (snd encIn encIntBin) (hS.comp (fst encIn encIntBin))

/-- Polynomial-time Nash witness extractor from any non-origin end-of-line basis pair `(T₁, T₂)`.
Produces the canonical bit-encoded pair `(x, y)` on well-formed games and `[]` otherwise. -/
def extractNash (p : BimatrixCode × List Bool) : List Bool :=
  let c := p.1
  let u := p.2
  if c.wellFormedB then
    let T₁ := decodeT₁ c u
    let T₂ := decodeT₂ c u
    let xp := normalizeRatPairs (extractStrategyNum c.rows (allRowsP c) (allIntRhsP c) T₁)
    let yp := normalizeRatPairs (extractStrategyNum c.cols (allRowsQ c) (allIntRhsQ c) T₂)
    encWitnessPairs (xp, yp)
  else []

private theorem extractNash_polytime :
    ComputableInPolyTime extractNash (encPair encBimatrix encBits) encBits := by
  have hc := fst encBimatrix encBits
  have h1 : ComputableInPolyTime (fun p : BimatrixCode × List Bool => decodeT₁ p.1 p.2)
      (encPair encBimatrix encBits) (encList encUnary) := decodeT₁_polytime
  have h2 : ComputableInPolyTime (fun p : BimatrixCode × List Bool => decodeT₂ p.1 p.2)
      (encPair encBimatrix encBits) (encList encUnary) := decodeT₂_polytime
  have hxp := normalizeRatPairs_polytime
    (extractStrategyNum_polytime (codeRows_polytime.comp hc) (allRowsP_polytime.comp hc)
      (allIntRhsP_polytime.comp hc) h1)
  have hyp := normalizeRatPairs_polytime
    (extractStrategyNum_polytime (codeCols_polytime.comp hc) (allRowsQ_polytime.comp hc)
      (allIntRhsQ_polytime.comp hc) h2)
  have hreenc : ComputableInPolyTime (fun z : List (ℤ × ℕ) × List (ℤ × ℕ) => encWitnessPairs z)
      encWitnessPairs encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  unfold extractNash
  exact (ite' (wellFormedB_polytime.comp hc) (hreenc.comp (hxp.prod hyp)) (const [])).of_enc_eq
    fun _ => rfl

private lemma extractStrategyNum_spec {m n k : ℕ}
    (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ) (b_int : Fin m ⊕ Fin n → ℤ)
    (allRows : List (List ℤ)) (allRhs : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), allRhs.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) :
    have hcard : (finsetOfList m n T).card = k := (card_finsetOfList hsort.nodup hlt).trans hlen
    let nums := extractStrategyNum k allRows allRhs T
    nums.length = k ∧
      ∀ i : Fin k, nums.getD i.1 0 = basisSignNum M_int b_int (finsetOfList m n T) hcard i := by
  intro hcard nums
  obtain ⟨hsub_len, _, hsub_det⟩ := subRows_eq_basisMat M_int allRows hall hsort hlt hlen
  obtain ⟨hcv_len, hcv_get⟩ :=
    cramerVecRows_eq_cramerVec M_int b_int allRows allRhs hall hrhs hsort hlt hlen
  refine ⟨by simp [nums, extractStrategyNum, hcv_len], fun i => ?_⟩
  dsimp only [nums, extractStrategyNum]
  rw [list_getD_map_lt _ _ 0 0 (by rw [hcv_len]; exact i.2), hsub_det, hcv_get i]
  rfl

private lemma normalizeRatPairs_spec {k : ℕ} {nums : List ℤ} (hlen : nums.length = k)
    (hnn : ∀ i : Fin k, 0 ≤ nums.getD i.1 0) (hpos : 0 < nums.sum) :
    let ps := normalizeRatPairs nums
    ps.length = k ∧ ps.all isCanonicalNonnegPair = true ∧
      ∀ i : Fin k, (ps.map mkRatOfPair).getD i.1 0 = (nums.getD i.1 0 : ℚ) / (nums.sum : ℚ) := by
  intro ps
  have hmem_nn : ∀ x ∈ nums, 0 ≤ x := by
    intro x hx
    rcases List.mem_iff_getElem.1 hx with ⟨i, hi, rfl⟩
    have hi' : i < k := hlen ▸ hi
    simpa only [List.getD_eq_getElem nums 0 hi] using hnn ⟨i, hi'⟩
  refine ⟨by simp [ps, normalizeRatPairs, hlen], ?_, ?_⟩
  · rw [List.all_eq_true]
    intro pq hpq
    rcases List.mem_map.1 hpq with ⟨num, hnum, rfl⟩
    exact (reduceIntPair_spec (hmem_nn num hnum) hpos).1
  · intro i
    have hi : i.1 < ps.length := by simp [ps, normalizeRatPairs, hlen, i.2]
    rw [list_getD_map_lt mkRatOfPair ps default 0 hi]
    dsimp only [ps, normalizeRatPairs]
    rw [list_getD_map_lt (fun num => reduceIntPair num nums.sum) nums 0 default
      (by rw [hlen]; exact i.2)]
    exact (reduceIntPair_spec (hnn i) hpos).2

/-- Lower bound on the framed bit-length of `encList enc l` from an elementwise lower bound. -/
theorem length_encList_ge_mul {α : Type*} (enc : α ↪ List Bool) (l : List α) (K : ℕ)
    (hK : ∀ a ∈ l, K ≤ (enc a).length) : l.length * (2 * K + 1) ≤ (encList enc l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
    have ha := hK a (by simp)
    have hl := ih fun b hb => hK b (by simp [hb])
    omega

private lemma size_prod_le {α : Type*} (l : List α) (f w : α → ℕ)
    (h : ∀ x ∈ l, (f x).size ≤ w x) : (l.map f).prod.size ≤ (l.map w).sum + 1 := by
  have hp := Int.size_natAbs_prod_le ((l.map f).map (Nat.cast : ℕ → ℤ))
  rw [← Nat.cast_list_prod, Int.natAbs_natCast, List.map_map, List.map_map] at hp
  have hsum : (l.map fun x => ((f x : ℤ).natAbs.size)).sum ≤ (l.map w).sum :=
    List.sum_le_sum fun x hx => by simpa only [Int.natAbs_natCast] using h x hx
  exact hp.trans (Nat.add_le_add_right hsum 1)

private lemma natAbs_prod_mat (M : List (List ℚ)) :
    Int.natAbs ((M.map fun row : List ℚ => (row.map fun q => (q.den : ℤ)).prod).prod) =
      (M.map fun row : List ℚ => (row.map fun q => q.den).prod).prod := by
  induction M with
  | nil => simp
  | cons row M ih =>
    simp only [List.map_cons, List.prod_cons, Int.natAbs_mul, ih]
    congr 1
    clear ih
    induction row with
    | nil => simp
    | cons q row ih =>
      simp only [List.map_cons, List.prod_cons, Int.natAbs_mul, Int.natAbs_natCast, ih]

private lemma natAbs_sum_mat (D : ℤ) (M : List (List ℚ)) :
    ((M.map fun row : List ℚ => (row.map fun q => (scaledEntry D q).natAbs).sum).sum : ℤ) =
      (M.map fun row : List ℚ => (row.map fun q => |scaledEntry D q|).sum).sum := by
  induction M with
  | nil => simp
  | cons row M ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    congr 1
    clear ih
    induction row with
    | nil => simp
    | cons q row ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
      exact congrArg (· + _) (Int.natCast_natAbs _)

private lemma size_HVal_and_dims_le {c : BimatrixCode} (hc : c.WellFormed) :
    38 * c.rows * c.cols + 1 ≤ (encBimatrix c).length ∧
      (HVal c).size ≤ 4 * (encBimatrix c).length + 4 := by
  set L := (encBimatrix c).length
  have hL : L = 2 * (encList (encList encRat) c.matA).length + 1 +
      (encList (encList encRat) c.matB).length := by
    dsimp only [L]
    rw [encBimatrix_apply, length_encPair]
  have hlen1_le : (encList (encList encRat) c.matA).length ≤ L := by omega
  have hlen2_le : (encList (encList encRat) c.matB).length ≤ L := by omega
  have hrows_cols : 38 * c.rows * c.cols + 1 ≤ L := by
    have hmat_len : ∀ M : List (List ℚ), M.length = c.rows →
        (∀ row ∈ M, row.length = c.cols) →
        c.rows * (2 * (c.cols * 9) + 1) ≤ (encList (encList encRat) M).length := by
      intro M hMlen hMrow
      have hrow_ge : ∀ row ∈ M, c.cols * 9 ≤ (encList encRat row).length := by
        intro row hrow
        rw [← hMrow row hrow]
        exact length_encList_ge_mul encRat row 4 fun q _ =>
          Turing.MultiTapeTM.four_le_length_encRat q
      have hm_ge := length_encList_ge_mul (encList encRat) M (c.cols * 9) hrow_ge
      rwa [hMlen] at hm_ge
    have h1_ge := hmat_len c.matA rfl hc.2.2.2.1
    have h2_ge := hmat_len c.matB hc.2.2.1 hc.2.2.2.2
    have hmul_eq : c.rows * (2 * (c.cols * 9) + 1) = 18 * (c.rows * c.cols) + c.rows := by ring
    rw [hmul_eq] at h1_ge h2_ge
    rw [mul_assoc]
    omega
  have hprod_mat_le : ∀ M : List (List ℚ),
      Nat.size ((M.map fun row : List ℚ => (row.map fun q => q.den).prod).prod) ≤
        (encList (encList encRat) M).length + 1 := by
    intro M
    refine size_prod_le M _ (fun row => 2 * (encList encRat row).length + 1) ?_ |>.trans ?_
    · intro row _
      have hrow_p : Nat.size (row.map fun q => q.den).prod ≤
          (row.map fun q => (encRat q).length).sum + 1 :=
        size_prod_le row _ (fun q => (encRat q).length) fun q _ => by
          have hlen_eq := Turing.MultiTapeTM.length_encRat q
          omega
      have hsum_le :=
        hrow_p.trans (Nat.add_le_add_right (sum_length_le_length_encList encRat row) 1)
      omega
    · rw [← length_encList (encList encRat) M]
  have hD_size : (clearScale c).natAbs.size ≤ L := by
    have h1 := hprod_mat_le c.matA
    have h2 := hprod_mat_le c.matB
    have hm := Nat.size_mul_le
      (c.matA.map fun row : List ℚ => (row.map fun q => q.den).prod).prod
      (c.matB.map fun row : List ℚ => (row.map fun q => q.den).prod).prod
    have hnat : (clearScale c).natAbs =
        (c.matA.map fun row : List ℚ => (row.map fun q => q.den).prod).prod *
          (c.matB.map fun row : List ℚ => (row.map fun q => q.den).prod).prod := by
      dsimp only [clearScale]
      rw [Int.natAbs_mul, natAbs_prod_mat, natAbs_prod_mat]
    have hne0 : 1 ≤ (encList (encList encRat) c.matA).length := by
      have h1_ge := length_encList_ge_mul (encList encRat) c.matA 0 fun _ _ => Nat.zero_le _
      have hr : 1 ≤ c.matA.length := hc.1
      omega
    rw [hnat]
    omega
  have hsum_mat_le : ∀ M : List (List ℚ), (encList (encList encRat) M).length ≤ L →
      Nat.size ((M.map fun row : List ℚ =>
          (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum) ≤ 4 * L := by
    intro M hML
    have hM_len : M.length ≤ L := (length_le_length_encList (encList encRat) M).trans hML
    have hM_sum := Nat.size_sum_le
      (l := M.map fun row : List ℚ =>
        (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum)
      (b := 3 * L) fun s hs => by
        rcases List.mem_map.1 hs with ⟨row, hrow, rfl⟩
        have hrow_enc : (encList encRat row).length ≤ L :=
          (length_le_encList_of_mem (encList encRat) hrow).trans hML
        have hrow_len : row.length ≤ L := (length_le_length_encList encRat row).trans hrow_enc
        have hrow_sum := Nat.size_sum_le
          (l := row.map fun q => (scaledEntry (clearScale c) q).natAbs) (b := 2 * L)
          fun s' hs' => by
            rcases List.mem_map.1 hs' with ⟨q, hq, rfl⟩
            have hq_enc : (encRat q).length ≤ L :=
              (length_le_encList_of_mem encRat hq).trans hrow_enc
            have hq_num : q.num.natAbs.size ≤ L := by
              have hlen_eq := Turing.MultiTapeTM.length_encRat q
              omega
            have hsc_le : (scaledEntry (clearScale c) q).natAbs ≤
                q.num.natAbs * (clearScale c).natAbs := by
              dsimp only [scaledEntry]
              rw [Int.natAbs_mul, Int.natAbs_tdiv, Int.natAbs_natCast]
              exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
            have hsc_size := (Nat.size_le_size hsc_le).trans (Nat.size_mul_le _ _)
            omega
        rw [List.length_map] at hrow_sum
        exact hrow_sum.trans (by
          have hl := (Nat.size_le_self row.length).trans hrow_len
          omega)
    rw [List.length_map] at hM_sum
    exact hM_sum.trans (by
      have hl := (Nat.size_le_self M.length).trans hM_len
      omega)
  have hs1 := hsum_mat_le c.matA hlen1_le
  have hs2 := hsum_mat_le c.matB hlen2_le
  have hshift_nat : (shiftVal c).natAbs =
      1 + (c.matA.map fun row : List ℚ =>
          (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum +
        (c.matB.map fun row : List ℚ =>
          (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum := by
    have hs_pos : 0 ≤ shiftVal c := le_of_lt (shiftVal_pos c)
    apply Nat.cast_injective (R := ℤ)
    rw [Int.natAbs_of_nonneg hs_pos]
    dsimp only [shiftVal]
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, natAbs_sum_mat, natAbs_sum_mat]
  have hshift_size : (shiftVal c).natAbs.size ≤ 4 * L + 2 := by
    rw [hshift_nat]
    have ha := Nat.size_add_le_max
      (1 + (c.matA.map fun row : List ℚ =>
        (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum)
      (c.matB.map fun row : List ℚ =>
        (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum
    have hb := Nat.size_add_le_max 1
      (c.matA.map fun row : List ℚ =>
        (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum
    have h1_size : (1 : ℕ).size = 1 := by decide
    omega
  have hH_size : (HVal c).size ≤ 4 * L + 4 := by
    dsimp only [HVal]
    have hm := Nat.size_mul_le 2 (shiftVal c).natAbs
    have h2_size : (2 : ℕ).size = 2 := by decide
    omega
  exact ⟨hrows_cols, hH_size⟩

private lemma length_encList_ratData_le {ps : List (ℤ × ℕ)} {k B : ℕ} (hlen : ps.length = k)
    (hbd : ∀ p ∈ ps, p.1.natAbs.size ≤ B ∧ p.2.size ≤ B) :
    (encList encRatData ps).length ≤ k * (6 * B + 7) := by
  rw [length_encList]
  have hsum : ∀ l : List (ℤ × ℕ),
      (∀ p ∈ l, p.1.natAbs.size ≤ B ∧ p.2.size ≤ B) →
        (l.map fun p => 2 * (encRatData p).length + 1).sum ≤ l.length * (6 * B + 7) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      have ⟨h1, h2⟩ := hl a List.mem_cons_self
      have hlen_p : (encRatData a).length = 2 * (a.1.natAbs.size + 1) + 1 + a.2.size := by
        simp only [length_encPair, length_encIntBin, encNat_apply, Nat.size_eq_bits_len]
      have hl_sum := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  simpa only [hlen] using hsum ps hbd

private lemma isRationalNash_of_toGame_isNash {c : BimatrixCode} {x y : List ℚ}
    (hx_len : x.length = c.rows) (hy_len : y.length = c.cols)
    (hx_nn : ∀ q ∈ x, 0 ≤ q) (hx_sum : x.sum = 1)
    (hy_nn : ∀ q ∈ y, 0 ≤ q) (hy_sum : y.sum = 1)
    (hGameNash : c.toGame.IsNash (fun i : Fin c.rows => (x.getD i.1 0 : ℝ))
      (fun j : Fin c.cols => (y.getD j.1 0 : ℝ))) :
    c.IsRationalNash x y := by
  rw [BimatrixGame.isNash_iff, BimatrixGame.isBestResponse₁_iff,
    BimatrixGame.isBestResponse₂_iff] at hGameNash
  rcases hGameNash with ⟨⟨hmx, hbr1R⟩, ⟨hmy, hbr2R⟩⟩
  let xR : Fin c.rows → ℝ := fun i => (x.getD i.1 0 : ℝ)
  let yR : Fin c.cols → ℝ := fun j => (y.getD j.1 0 : ℝ)
  have hxR_nn : ∀ i, 0 ≤ xR i := (isMixedStrategy_iff.1 hmx).1
  have hxR_sum : ∑ i : Fin c.rows, xR i = 1 := (isMixedStrategy_iff.1 hmx).2
  have hyR_nn : ∀ j, 0 ≤ yR j := (isMixedStrategy_iff.1 hmy).1
  have hyR_sum : ∑ j : Fin c.cols, yR j = 1 := (isMixedStrategy_iff.1 hmy).2
  refine ⟨hx_len, hy_len, hx_nn, hx_sum, hy_nn, hy_sum, fun i => ?_, fun j => ?_⟩
  · rw [← Rat.cast_le (K := ℝ)]
    have hstep : ∀ a : Fin c.rows,
        xR a * (c.toGame.A *ᵥ yR) i ≤ xR a * (c.toGame.A *ᵥ yR) a := fun a => by
      rcases eq_or_lt_of_le (hxR_nn a) with ha0 | hapos
      · rw [← ha0, zero_mul, zero_mul]
      · have hpb := (BimatrixGame.isPureBestResponse₁_iff.1 (hbr1R a hapos)) i
        exact mul_le_mul_of_nonneg_left hpb (hxR_nn a)
    have hsum_le : (∑ a : Fin c.rows, xR a * (c.toGame.A *ᵥ yR) i) ≤
        ∑ a : Fin c.rows, xR a * (c.toGame.A *ᵥ yR) a :=
      Finset.sum_le_sum fun a _ => hstep a
    rw [← Finset.sum_mul, hxR_sum, one_mul] at hsum_le
    simpa only [xR, yR, toGame, Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum,
      Rat.cast_mul, Finset.mul_sum, mul_assoc] using hsum_le
  · rw [← Rat.cast_le (K := ℝ)]
    have hstep : ∀ b : Fin c.cols,
        (xR ᵥ* c.toGame.B) j * yR b ≤ (xR ᵥ* c.toGame.B) b * yR b := fun b => by
      rcases eq_or_lt_of_le (hyR_nn b) with hb0 | hbpos
      · rw [← hb0, mul_zero, mul_zero]
      · have hpb := (BimatrixGame.isPureBestResponse₂_iff.1 (hbr2R b hbpos)) j
        exact mul_le_mul_of_nonneg_right hpb (hyR_nn b)
    have hsum_le : (∑ b : Fin c.cols, (xR ᵥ* c.toGame.B) j * yR b) ≤
        ∑ b : Fin c.cols, (xR ᵥ* c.toGame.B) b * yR b :=
      Finset.sum_le_sum fun b _ => hstep b
    rw [← Finset.mul_sum, hyR_sum, mul_one] at hsum_le
    simp only [xR, yR, toGame, Matrix.vecMul, dotProduct, Matrix.map_apply, Rat.cast_sum,
      Rat.cast_mul, Finset.sum_mul, mul_assoc] at hsum_le ⊢
    rw [Finset.sum_comm] at hsum_le
    exact hsum_le

private lemma strategy_pair_size_bd {k H L : ℕ} (hkL : k ≤ L) (hH_sz : H.size ≤ 4 * L + 4)
    {num_l : List ℤ} (hlen : num_l.length = k)
    (hbd : ∀ i : Fin k, |num_l.getD i.1 0| ≤ ((k.factorial * H ^ k : ℕ) : ℤ))
    (hpos : 0 < num_l.sum) :
    ∀ pq ∈ normalizeRatPairs num_l,
      pq.1.natAbs.size ≤ k * (5 * L + 5) + 2 ∧ pq.2.size ≤ k * (5 * L + 5) + 2 := by
  intro pq hpq
  rcases List.mem_map.1 hpq with ⟨num, hnum, rfl⟩
  rcases List.mem_iff_getElem.1 hnum with ⟨idx, hidx, rfl⟩
  have hidx' : idx < k := hlen ▸ hidx
  let i : Fin k := ⟨idx, hidx'⟩
  have hnum_eq : num_l[idx] = num_l.getD i.1 0 :=
    (List.getD_eq_getElem num_l 0 hidx).symm
  have hbd_num : num_l[idx].natAbs ≤ k.factorial * H ^ k := by
    rw [hnum_eq]
    have hbi := hbd i
    rw [← Int.natCast_natAbs] at hbi
    exact Int.ofNat_le.1 hbi
  have hbd_sum : num_l.sum.natAbs ≤ k * (k.factorial * H ^ k) := by
    have hS_nn : 0 ≤ num_l.sum := hpos.le
    have hS_Z : (num_l.sum : ℤ) ≤ ((k * (k.factorial * H ^ k) : ℕ) : ℤ) := by
      rw [← fin_sum_getD_eq_list_sum num_l 0 hlen]
      calc ∑ i' : Fin k, num_l.getD i'.1 0
          ≤ ∑ _i' : Fin k, ((k.factorial * H ^ k : ℕ) : ℤ) :=
            Finset.sum_le_sum fun i' _ => (le_abs_self _).trans (hbd i')
        _ = ((k * (k.factorial * H ^ k) : ℕ) : ℤ) := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_mul]
    exact Int.ofNat_le.1 (by simpa only [Int.natAbs_of_nonneg hS_nn] using hS_Z)
  have hfac := Nat.size_factorial_le k
  have hpow := Nat.size_pow_le H k
  have hks := Nat.size_le_self k
  have hbase_sz : (k.factorial * H ^ k).size ≤ k * (5 * L + 4) + 2 := by
    have hm := Nat.size_mul_le k.factorial (H ^ k)
    have hkk : k * k.size ≤ k * L := Nat.mul_le_mul_left k (hks.trans hkL)
    have hkH : k * H.size ≤ k * (4 * L + 4) := Nat.mul_le_mul_left k hH_sz
    have hmul : k * L + 1 + (k * (4 * L + 4) + 1) = k * (5 * L + 4) + 2 := by ring
    omega
  have hsum_sz : num_l.sum.natAbs.size ≤ k * (5 * L + 5) + 2 := by
    have hs := (Nat.size_le_size hbd_sum).trans (Nat.size_mul_le _ _)
    have hsum_eq : k + (k * (5 * L + 4) + 2) = k * (5 * L + 5) + 2 := by ring
    omega
  have hnum_sz : num_l[idx].natAbs.size ≤ k * (5 * L + 5) + 2 := by
    have hs := (Nat.size_le_size hbd_num).trans hbase_sz
    have hle : k * (5 * L + 4) ≤ k * (5 * L + 5) := Nat.mul_le_mul_left k (by omega)
    omega
  dsimp only [reduceIntPair]
  rw [Int.natAbs_natCast]
  exact ⟨(Nat.size_le_size (Nat.div_le_self _ _)).trans hnum_sz,
    (Nat.size_le_size (Nat.div_le_self _ _)).trans hsum_sz⟩

private lemma witness_length_arith {m n L ax ay : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hrc : 38 * m * n + 1 ≤ L)
    (hx : ax ≤ m * (6 * (m * (5 * L + 5) + 2) + 7))
    (hy : ay ≤ n * (6 * (n * (5 * L + 5) + 2) + 7)) :
    2 * ax + 1 + ay ≤ 120 * L ^ 3 + 400 * L + 100 := by
  have hm_le : 38 * m ≤ L := by
    calc 38 * m = 38 * m * 1 := (mul_one _).symm
      _ ≤ 38 * m * n := Nat.mul_le_mul_left _ hn
      _ ≤ L := by omega
  have hn_le : 38 * n ≤ L := by
    calc 38 * n = 38 * 1 * n := by ring
      _ ≤ 38 * m * n := Nat.mul_le_mul_right n (Nat.mul_le_mul_left 38 hm)
      _ ≤ L := by omega
  have hm2_le : 1444 * m ^ 2 ≤ L ^ 2 := by
    calc 1444 * m ^ 2 = (38 * m) * (38 * m) := by ring
      _ ≤ L * L := Nat.mul_le_mul hm_le hm_le
      _ = L ^ 2 := (sq L).symm
  have hn2_le : 1444 * n ^ 2 ≤ L ^ 2 := by
    calc 1444 * n ^ 2 = (38 * n) * (38 * n) := by ring
      _ ≤ L * L := Nat.mul_le_mul hn_le hn_le
      _ = L ^ 2 := (sq L).symm
  have hm2L_le : 1444 * (m ^ 2 * L) ≤ L ^ 3 := by
    calc 1444 * (m ^ 2 * L) = 1444 * m ^ 2 * L := (mul_assoc _ _ _).symm
      _ ≤ L ^ 2 * L := Nat.mul_le_mul_right L hm2_le
      _ = L ^ 3 := by ring
  have hn2L_le : 1444 * (n ^ 2 * L) ≤ L ^ 3 := by
    calc 1444 * (n ^ 2 * L) = 1444 * n ^ 2 * L := (mul_assoc _ _ _).symm
      _ ≤ L ^ 2 * L := Nat.mul_le_mul_right L hn2_le
      _ = L ^ 3 := by ring
  have h1 : m * (6 * (m * (5 * L + 5) + 2) + 7) = 30 * (m ^ 2 * L) + 30 * m ^ 2 + 19 * m := by
    ring
  have h2 : n * (6 * (n * (5 * L + 5) + 2) + 7) = 30 * (n ^ 2 * L) + 30 * n ^ 2 + 19 * n := by
    ring
  rw [h1] at hx
  rw [h2] at hy
  have hm2L_le' : 30 * (m ^ 2 * L) ≤ L ^ 3 :=
    (Nat.mul_le_mul_right (m ^ 2 * L) (by decide : 30 ≤ 1444)).trans hm2L_le
  have hn2L_le' : 30 * (n ^ 2 * L) ≤ L ^ 3 :=
    (Nat.mul_le_mul_right (n ^ 2 * L) (by decide : 30 ≤ 1444)).trans hn2L_le
  have hm2_le' : 30 * m ^ 2 ≤ L ^ 2 := by omega
  have hn2_le' : 30 * n ^ 2 ≤ L ^ 2 := by omega
  have hL : 1 ≤ L := by
    have h38 : 38 ≤ 38 * m * n :=
      calc 38 = 38 * 1 * 1 := by ring
        _ ≤ 38 * m * 1 := Nat.mul_le_mul_right 1 (Nat.mul_le_mul_left 38 hm)
        _ ≤ 38 * m * n := Nat.mul_le_mul_left (38 * m) hn
    omega
  have hL2_le : L ^ 2 ≤ L ^ 3 := by
    calc L ^ 2 = L ^ 2 * 1 := (mul_one _).symm
      _ ≤ L ^ 2 * L := Nat.mul_le_mul_left _ hL
      _ = L ^ 3 := by ring
  have hax : ax ≤ 2 * L ^ 3 + L := by
    have hm1 : 19 * m ≤ L := by omega
    have hm2_le3 : 30 * m ^ 2 ≤ L ^ 3 := hm2_le'.trans hL2_le
    calc ax ≤ 30 * (m ^ 2 * L) + 30 * m ^ 2 + 19 * m := hx
      _ ≤ L ^ 3 + L ^ 3 + L := Nat.add_le_add (Nat.add_le_add hm2L_le' hm2_le3) hm1
      _ = 2 * L ^ 3 + L := by ring
  have hay : ay ≤ 2 * L ^ 3 + L := by
    have hn1 : 19 * n ≤ L := by omega
    have hn2_le3 : 30 * n ^ 2 ≤ L ^ 3 := hn2_le'.trans hL2_le
    calc ay ≤ 30 * (n ^ 2 * L) + 30 * n ^ 2 + 19 * n := hy
      _ ≤ L ^ 3 + L ^ 3 + L := Nat.add_le_add (Nat.add_le_add hn2L_le' hn2_le3) hn1
      _ = 2 * L ^ 3 + L := by ring
  calc 2 * ax + 1 + ay
      ≤ 2 * (2 * L ^ 3 + L) + 1 + (2 * L ^ 3 + L) :=
        Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hax) 1) hay
    _ = 6 * L ^ 3 + 3 * L + 1 := by ring
    _ ≤ 120 * L ^ 3 + 400 * L + 100 := by
        refine Nat.add_le_add (Nat.add_le_add ?_ ?_) (by decide)
        · exact Nat.mul_le_mul_right _ (by decide)
        · exact Nat.mul_le_mul_right _ (by decide)

/-- Every vertex solving `endOfLineRel vertexLen pred succ c` extracts via `extractNash` to a
solution of `BimatrixNash c`. -/
theorem extractNash_sound {c : BimatrixCode} {u : List Bool}
    (hu : endOfLineRel vertexLen pred succ c u) :
    BimatrixNash c (extractNash (c, u)) := by
  by_cases hwb : c.wellFormedB = true
  · have hc : c.WellFormed := (wellFormed_iff_wellFormedB c).2 hwb
    obtain ⟨hu_valid, hu_ne0, hcl0⟩ := endOfLineRel_wellFormed_props hc hu
    obtain ⟨hlen_u, hlen₁, hlen₂, hacl, hcard₁, hcard₂, hfb₁, hfb₂⟩ := validNode_props hc hu_valid
    let T₁ := decodeT₁ c u
    let T₂ := decodeT₂ c u
    let T₁s := finsetOfList c.rows c.cols T₁
    let T₂s := finsetOfList c.rows c.cols T₂
    have huniv : T₁s ∪ T₂s = Finset.univ := by
      ext k
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hk : k = Sum.inl ⟨0, hc.1⟩
      · subst hk
        rcases hcl0 with h0 | h0
        · exact .inl (mem_finsetOfList.2 h0)
        · exact .inr (mem_finsetOfList.2 h0)
      · exact hacl k hk
    have hne0 : (T₁s, T₂s) ≠ (Finset.univ.image Sum.inl, Finset.univ.image Sum.inr) := by
      intro heq
      have h1_eq : T₁s = Finset.univ.image Sum.inl := congrArg Prod.fst heq
      have h2_eq : T₂s = Finset.univ.image Sum.inr := congrArg Prod.snd heq
      have hT₁_eq : T₁ = List.range c.rows := by
        have hperm : T₁.Perm (List.range c.rows) := by
          refine List.perm_of_nodup_nodup_toFinset_eq (decodeT₁_sorted c u).nodup
            List.nodup_range ?_
          ext k
          simp only [List.mem_toFinset, List.mem_range]
          constructor
          · intro hk
            have hmem : finSumFinEquiv.symm ⟨k, decodeT₁_lt c u hk⟩ ∈ T₁s := by
              rw [mem_finsetOfList, Equiv.apply_symm_apply]
              exact hk
            rw [h1_eq, Finset.mem_image] at hmem
            rcases hmem with ⟨i, _, hi⟩
            have hval := congrArg (fun z => (finSumFinEquiv z).1) hi
            simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, Fin.val_castAdd] at hval
            rw [← hval]
            exact i.2
          · intro hk
            have hmem : (Sum.inl ⟨k, hk⟩ : Fin c.rows ⊕ Fin c.cols) ∈
                Finset.univ.image Sum.inl := Finset.mem_image_of_mem _ (Finset.mem_univ _)
            rw [← h1_eq, mem_finsetOfList] at hmem
            exact hmem
        exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2))
          (decodeT₁_sorted c u) List.pairwise_lt_range
      have hT₂_eq : T₂ = (List.range c.cols).map (· + c.rows) := by
        have hsort_r : ((List.range c.cols).map (· + c.rows)).Pairwise (· < ·) :=
          List.pairwise_lt_range.map _ fun _ _ h => by omega
        have hperm : T₂.Perm ((List.range c.cols).map (· + c.rows)) := by
          refine List.perm_of_nodup_nodup_toFinset_eq (decodeT₂_sorted c u).nodup hsort_r.nodup ?_
          ext k
          simp only [List.mem_toFinset, List.mem_map, List.mem_range]
          constructor
          · intro hk
            have hmem : finSumFinEquiv.symm ⟨k, decodeT₂_lt c u hk⟩ ∈ T₂s := by
              rw [mem_finsetOfList, Equiv.apply_symm_apply]
              exact hk
            rw [h2_eq, Finset.mem_image] at hmem
            rcases hmem with ⟨j, _, hj⟩
            have hval := congrArg (fun z => (finSumFinEquiv z).1) hj
            simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right, Fin.val_natAdd] at hval
            exact ⟨j.1, j.2, by omega⟩
          · rintro ⟨j, hj, rfl⟩
            have hmem : (Sum.inr ⟨j, hj⟩ : Fin c.rows ⊕ Fin c.cols) ∈
                Finset.univ.image Sum.inr := Finset.mem_image_of_mem _ (Finset.mem_univ _)
            rw [← h2_eq, mem_finsetOfList] at hmem
            simpa only [finSumFinEquiv_apply_right, Fin.val_natAdd, Nat.add_comm] using hmem
        exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (Nat.lt_asymm h1 h2))
          (decodeT₂_sorted c u) hsort_r
      have hu_eq : u = zeroVertex (vertexLen c) := by
        have hvlen : vertexLen c = 2 * (c.rows + c.cols) := by
          simp only [vertexLen, hwb, ite_true]
        rw [hvlen, ← encodeNodes_origin c, ← hT₁_eq, ← hT₂_eq]
        exact (encodeNodes_decode hlen_u).symm
      exact hu_ne0 hu_eq
    have hH : 1 ≤ HVal c := (posMat_bounds hc ⟨0, hc.1⟩ ⟨0, hc.2.1⟩).1
    have hA_bd : ∀ i j, 1 ≤ posMatA c i j ∧ posMatA c i j ≤ (HVal c : ℤ) := fun i j =>
      ⟨(posMat_bounds hc i j).2.1, (posMat_bounds hc i j).2.2.1⟩
    have hB_bd : ∀ i j, 1 ≤ posMatB c i j ∧ posMatB c i j ≤ (HVal c : ℤ) := fun i j =>
      ⟨(posMat_bounds hc i j).2.2.2.1, (posMat_bounds hc i j).2.2.2.2⟩
    have hex := BimatrixGame.isNash_extractNum hc.1 hc.2.1 hH hA_bd hB_bd hfb₁ hfb₂ huniv hne0
    dsimp only at hex
    obtain ⟨hnumP_nn, hS₁_pos, hP_bd, hnumQ_nn, hS₂_pos, hQ_bd, hNashPos⟩ := hex
    obtain ⟨hnumP_len, hnumP_get⟩ := extractStrategyNum_spec (intMatP (posMatB c))
      (intRhsP c.rows c.cols) (allRowsP c) (allIntRhsP c) (allRowsP_spec c)
      (allIntRhsP_spec c) (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr) hlen₁
    obtain ⟨hnumQ_len, hnumQ_get⟩ := extractStrategyNum_spec (intMatQ (posMatA c))
      (intRhsQ c.rows c.cols) (allRowsQ c) (allIntRhsQ c) (allRowsQ_spec c)
      (allIntRhsQ_spec c) (decodeT₂_sorted c u) (fun _ hr => decodeT₂_lt c u hr) hlen₂
    let numP_l := extractStrategyNum c.rows (allRowsP c) (allIntRhsP c) T₁
    let numQ_l := extractStrategyNum c.cols (allRowsQ c) (allIntRhsQ c) T₂
    have hS₁_eq : numP_l.sum = ∑ i : Fin c.rows,
        basisSignNum (intMatP (posMatB c)) (intRhsP c.rows c.cols) T₁s hcard₁ i := by
      rw [← fin_sum_getD_eq_list_sum numP_l 0 hnumP_len]
      exact Finset.sum_congr rfl fun i _ => hnumP_get i
    have hS₂_eq : numQ_l.sum = ∑ j : Fin c.cols,
        basisSignNum (intMatQ (posMatA c)) (intRhsQ c.rows c.cols) T₂s hcard₂ j := by
      rw [← fin_sum_getD_eq_list_sum numQ_l 0 hnumQ_len]
      exact Finset.sum_congr rfl fun j _ => hnumQ_get j
    have hxp_spec := normalizeRatPairs_spec hnumP_len
      (fun i => by rw [hnumP_get i]; exact hnumP_nn i) (hS₁_eq ▸ hS₁_pos)
    have hyp_spec := normalizeRatPairs_spec hnumQ_len
      (fun j => by rw [hnumQ_get j]; exact hnumQ_nn j) (hS₂_eq ▸ hS₂_pos)
    let xp := normalizeRatPairs numP_l
    let yp := normalizeRatPairs numQ_l
    let x := xp.map mkRatOfPair
    let y := yp.map mkRatOfPair
    have hx_len : x.length = c.rows := by dsimp only [x, xp]; rw [List.length_map, hxp_spec.1]
    have hy_len : y.length = c.cols := by dsimp only [y, yp]; rw [List.length_map, hyp_spec.1]
    have hx_nn : ∀ q ∈ x, 0 ≤ q := by
      intro q hq
      rcases List.mem_map.1 hq with ⟨pq, hpq, rfl⟩
      have hcan := (List.all_eq_true.1 hxp_spec.2.1) pq hpq
      simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hcan
      exact div_nonneg (by exact_mod_cast hcan.1.1) (by exact_mod_cast Nat.zero_le pq.2)
    have hy_nn : ∀ q ∈ y, 0 ≤ q := by
      intro q hq
      rcases List.mem_map.1 hq with ⟨pq, hpq, rfl⟩
      have hcan := (List.all_eq_true.1 hyp_spec.2.1) pq hpq
      simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hcan
      exact div_nonneg (by exact_mod_cast hcan.1.1) (by exact_mod_cast Nat.zero_le pq.2)
    have hx_getR : (fun i : Fin c.rows => (x.getD i.1 0 : ℝ)) =
        fun i => ((basisSignNum (intMatP (posMatB c)) (intRhsP c.rows c.cols) T₁s hcard₁ i : ℤ) :
          ℝ) / ((∑ i : Fin c.rows,
            basisSignNum (intMatP (posMatB c)) (intRhsP c.rows c.cols) T₁s hcard₁ i : ℤ) : ℝ) := by
      ext i
      rw [hxp_spec.2.2 i, hnumP_get i, hS₁_eq]
      simp only [Rat.cast_div, Rat.cast_intCast]
      rfl
    have hy_getR : (fun j : Fin c.cols => (y.getD j.1 0 : ℝ)) =
        fun j => ((basisSignNum (intMatQ (posMatA c)) (intRhsQ c.rows c.cols) T₂s hcard₂ j : ℤ) :
          ℝ) / ((∑ j : Fin c.cols,
            basisSignNum (intMatQ (posMatA c)) (intRhsQ c.rows c.cols) T₂s hcard₂ j : ℤ) : ℝ) := by
      ext j
      rw [hyp_spec.2.2 j, hnumQ_get j, hS₂_eq]
      simp only [Rat.cast_div, Rat.cast_intCast]
      rfl
    have hGameNash : c.toGame.IsNash (fun i : Fin c.rows => (x.getD i.1 0 : ℝ))
        (fun j : Fin c.cols => (y.getD j.1 0 : ℝ)) := by
      rw [hx_getR, hy_getR]
      exact (isNash_posMat hc _ _).1 hNashPos
    have hx_sum : x.sum = 1 :=
      list_sum_eq_one_of_div hx_len hnumP_len (hS₁_eq ▸ hS₁_pos) hxp_spec.2.2
    have hy_sum : y.sum = 1 :=
      list_sum_eq_one_of_div hy_len hnumQ_len (hS₂_eq ▸ hS₂_pos) hyp_spec.2.2
    have hRatNash : c.IsRationalNash x y :=
      isRationalNash_of_toGame_isNash hx_len hy_len hx_nn hx_sum hy_nn hy_sum hGameNash
    have hex_pairs : extractNash (c, u) = encWitnessPairs (xp, yp) := by
      dsimp only [extractNash]
      simp only [hwb, ite_true]
      rfl
    have hw_eq : extractNash (c, u) = encWitness ⟨x, y⟩ := by
      rw [hex_pairs, encWitness_eq_pairs x y, map_pair_mkRatOfPair_eq hxp_spec.2.1,
        map_pair_mkRatOfPair_eq hyp_spec.2.1]
    obtain ⟨hrc, hH_size⟩ := size_HVal_and_dims_le hc
    set L := (encBimatrix c).length
    have hm_le_L : c.rows ≤ L := by
      have h1 :=
        calc c.rows ≤ 38 * c.rows * 1 := by omega
          _ ≤ 38 * c.rows * c.cols := Nat.mul_le_mul_left _ hc.2.1
      omega
    have hn_le_L : c.cols ≤ L := by
      have h1 :=
        calc c.cols ≤ 38 * 1 * c.cols := by omega
          _ ≤ 38 * c.rows * c.cols := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 38 hc.1)
      omega
    have hB1 := strategy_pair_size_bd hm_le_L hH_size hnumP_len
      (fun i => by rw [hnumP_get i]; exact hP_bd i) (hS₁_eq ▸ hS₁_pos)
    have hB2 := strategy_pair_size_bd hn_le_L hH_size hnumQ_len
      (fun j => by rw [hnumQ_get j]; exact hQ_bd j) (hS₂_eq ▸ hS₂_pos)
    have hlen_xp := length_encList_ratData_le hxp_spec.1 hB1
    have hlen_yp := length_encList_ratData_le hyp_spec.1 hB2
    have hlen_w : (extractNash (c, u)).length ≤ 120 * L ^ 3 + 400 * L + 100 := by
      rw [hex_pairs]
      change (encPair (encList encRatData) (encList encRatData) (xp, yp)).length ≤
        120 * L ^ 3 + 400 * L + 100
      rw [length_encPair]
      exact witness_length_arith hc.1 hc.2.1 hrc hlen_xp hlen_yp
    simp only [BimatrixNash, hwb, ite_true]
    exact ⟨hlen_w, ⟨x, y⟩, hw_eq, hRatNash⟩
  · have hwf : c.wellFormedB = false := Bool.eq_false_iff.2 hwb
    simp only [BimatrixNash, extractNash, hwf, Bool.false_eq_true, ite_false]

/-- Two-player rational Nash equilibrium search-reduces in polynomial time to the canonical
PPAD problem `endOfLineRel vertexLen pred succ`. -/
theorem BimatrixNash_searchReducible_endOfLineRel :
    SearchReducible encBimatrix encBimatrix BimatrixNash (endOfLineRel vertexLen pred succ) :=
  .of_isTotalSearch (isTotalSearch_endOfLineRel length_succ) ComputableInPolyTime.id'
    extractNash_polytime fun _ _ hw => extractNash_sound hw

/-- **Two-player rational Nash equilibrium is in `PPAD`.** -/
theorem BimatrixNash_mem_PPAD : BimatrixNash ∈ PPAD encBimatrix :=
  mem_PPAD.2 ⟨BimatrixNash_mem_FNP, vertexLen, pred, succ,
    vertexLen_polytime, pred_polytime, succ_polytime, length_pred, length_succ,
    BimatrixNash_searchReducible_endOfLineRel⟩

/-- **Two-player rational Nash equilibrium is in `TFNP`** (and hence total by Brouwer /
Lemke–Howson). -/
theorem BimatrixNash_mem_TFNP : BimatrixNash ∈ TFNP encBimatrix :=
  PPAD_subset_TFNP BimatrixNash_mem_PPAD

/-- **Totality of two-player Nash:** every encoded rational game has a valid rational Nash
equilibrium witness (or empty witness on malformed inputs). -/
theorem BimatrixNash_isTotalSearch : IsTotalSearch BimatrixNash :=
  BimatrixNash_mem_TFNP.2

/-- **Reduction to circuit `EndOfLine`:** two-player rational Nash search-reduces in polynomial
time to canonical circuit `EndOfLine`. -/
theorem BimatrixNash_searchReducible_EndOfLine :
    SearchReducible encBimatrix encEndOfLine BimatrixNash EndOfLine :=
  EndOfLine_searchComplete.2 _ _ BimatrixNash_mem_PPAD

end BimatrixCode

end Cslib.GameTheory
