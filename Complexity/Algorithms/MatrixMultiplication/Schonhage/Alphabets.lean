/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.DeriveFintype

/-!
# The alphabets and coefficient forms of Schönhage's tensor

Seven left variables, seven right variables, ten output variables and ten multiplication
terms are represented explicitly. Indices start at zero. Linear forms are coefficient
functions over integers; no arithmetic operation is treated as a native machine instruction.

## Main definitions

* `LeftVar`, `RightVar`, `OutVar`, `Term`: the four finite alphabets.
* `phi`, `psi`, `chi`: the left, right and output coefficient forms.
* `Term.Contributes`: occurrence in an output form.

## Main results

* `card_leftVar`, `card_rightVar`, `card_term`: alphabet sizes.
* `Term.contributes_iff`, `chi_eq_ite`: output incidence and its coefficient.

## References

Part of [AlmanWilliams2026, Section 2]. Direct mathematical adaptation of
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Definitions are selectively extracted from that pin's `PaperStatements.lean`; no machine
semantics or running-time statement is imported. The docstrings below explain the local
declarations in our own words.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Left input coordinates: three `x` coordinates and a two-by-two family of `p` coordinates. -/
inductive LeftVar : Type
  | x (i : Fin 3)
  | p (i j : Fin 2)
  deriving DecidableEq, Fintype

/-- Right input coordinates: three `y` coordinates and a two-by-two family of `q` coordinates. -/
inductive RightVar : Type
  | y (j : Fin 3)
  | q (i j : Fin 2)
  deriving DecidableEq, Fintype

/-- Output coordinates comprise a three-by-three outer family and one distinguished inner
coordinate.
-/
inductive OutVar : Type
  | z (i j : Fin 3)
  | z0
  deriving DecidableEq, Fintype

/-- The multiplication labels consist of nine indexed labels `P i j` and the additional label
`P0`.
-/
inductive Term : Type
  | P (i j : Fin 3)
  | P0
  deriving DecidableEq, Fintype

/-- The linear form consisting of the single left variable `x_i`.
-/
def xForm (i : Fin 3) : LeftVar → ℤ := Pi.single (LeftVar.x i) 1
/-- The linear form consisting of the single left variable `p_ij`.
-/
def pForm (i j : Fin 2) : LeftVar → ℤ := Pi.single (LeftVar.p i j) 1
/-- The linear form consisting of the single right variable `y_j`.
-/
def yForm (j : Fin 3) : RightVar → ℤ := Pi.single (RightVar.y j) 1
/-- The linear form consisting of the single right variable `q_ij`.
-/
def qForm (i j : Fin 2) : RightVar → ℤ := Pi.single (RightVar.q i j) 1
/-- The linear form consisting of the single output variable `z_ij`.
-/
def zForm (i j : Fin 3) : OutVar → ℤ := Pi.single (OutVar.z i j) 1
/-- The linear form consisting of the single output variable `z₀`.
-/
def z0Form : OutVar → ℤ := Pi.single OutVar.z0 1

/-- Extend the two-by-two `p` family to three rows by cancelling each column sum; the third column
is zero.
-/
def pHat : Matrix (Fin 3) (Fin 3) (LeftVar → ℤ) :=
  !![pForm 0 0, pForm 0 1, 0;
     pForm 1 0, pForm 1 1, 0;
     -pForm 0 0 - pForm 1 0, -pForm 0 1 - pForm 1 1, 0]

/-- Extend the two-by-two `q` family to three columns by cancelling each row sum; the third row is
zero.
-/
def qHat : Matrix (Fin 3) (Fin 3) (RightVar → ℤ) :=
  !![qForm 0 0, qForm 0 1, -qForm 0 0 - qForm 0 1;
     qForm 1 0, qForm 1 1, -qForm 1 0 - qForm 1 1;
     0, 0, 0]

/-- Left coefficients for each multiplication label. An indexed label adds its `x` coordinate to
the corresponding `pHat` form; `P0` negates the sum of the three `x` coordinates.
-/
def phi : Term → LeftVar → ℤ
  | .P i j => xForm i + pHat i j
  | .P0 => -(xForm 0 + xForm 1 + xForm 2)

/-- Right coefficients for each multiplication label. Indexed labels use `y` plus `qHat`, whereas
`P0` uses the sum of the three `y` coordinates.
-/
def psi : Term → RightVar → ℤ
  | .P i j => yForm j + qHat i j
  | .P0 => yForm 0 + yForm 1 + yForm 2

/-- Output coefficients: each indexed label occurs in its own outer coordinate and in `z0`; `P0`
occurs only in `z0`.
-/
def chi : Term → OutVar → ℤ
  | .P i j => zForm i j + z0Form
  | .P0 => z0Form

/-- Select the distinguished output coordinate, excluding the indexed outer coordinates. -/
def OutVar.IsInner : OutVar → Prop
  | .z _ _ => False
  | .z0 => True

instance OutVar.instDecidablePredIsInner : DecidablePred OutVar.IsInner
  | .z _ _ => isFalse fun h => h
  | .z0 => isTrue trivial

/-- A label is relevant to an output coordinate when its output coefficient is nonzero. -/
def Term.Contributes (lam : Term) (z : OutVar) : Prop := chi lam z ≠ 0

instance Term.instDecidableContributes (lam : Term) (z : OutVar) : Decidable (lam.Contributes z) :=
  inferInstanceAs (Decidable (chi lam z ≠ 0))

/-- Choose the indexed label for an outer coordinate and `P0` for the inner coordinate. Applying
this choice coordinatewise defines a private leaf.
-/
def OutVar.privateTerm : OutVar → Term
  | .z i j => .P i j
  | .z0 => .P0

/-- A length-`L` tuple of left coordinates, indexed from zero. -/
abbrev LeftStr (L : ℕ) : Type := Fin L → LeftVar
/-- A length-`L` tuple with entries in `RightVar`. -/
abbrev RightStr (L : ℕ) : Type := Fin L → RightVar
/-- A length-`L` tuple with entries in `OutVar`. -/
abbrev OutStr (L : ℕ) : Type := Fin L → OutVar
/-- The sequence of multiplication labels identifying a depth-`k` recursion vertex. -/
abbrev Vertex (k : ℕ) : Type := Fin k → Term
/-- A terminal vertex, whose label sequence has the full recursion depth. -/
abbrev Leaf (L : ℕ) : Type := Vertex L

/-! ### The alphabets -/

/-- The left variables, listed: `x i` is `.inl i`, and `p i j` is `.inr (i, j)`.
-/
def LeftVar.equiv : LeftVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .x i => .inl i
    | .p i j => .inr (i, j)
  invFun
    | .inl i => .x i
    | .inr (i, j) => .p i j
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | ⟨_, _⟩ <;> rfl

/-- The right variables, listed: `y j` is `.inl j`, and `q i j` is `.inr (i, j)`.
-/
def RightVar.equiv : RightVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .y j => .inl j
    | .q i j => .inr (i, j)
  invFun
    | .inl j => .y j
    | .inr (i, j) => .q i j
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- The terms, listed: `P i j` is `some (i, j)`, and `P0` is `none`.
-/
def Term.equiv : Term ≃ Option (Fin 3 × Fin 3) where
  toFun
    | .P i j => some (i, j)
    | .P0 => none
  invFun
    | some (i, j) => .P i j
    | none => .P0
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- The left alphabet has cardinality seven. -/
theorem card_leftVar : Fintype.card LeftVar = 7 := by
  simp [Fintype.card_congr LeftVar.equiv]

/-- The right alphabet has cardinality seven. -/
theorem card_rightVar : Fintype.card RightVar = 7 := by
  simp [Fintype.card_congr RightVar.equiv]

/-- There are ten multiplication labels. -/
theorem card_term : Fintype.card Term = 10 := by
  simp [Fintype.card_congr Term.equiv]

/-! ### Which terms contribute to which output variables -/

/-- The inner coordinate receives a contribution from every multiplication label. -/
@[simp]
theorem Term.contributes_z0 (lam : Term) : lam.Contributes .z0 := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form]

/-- For an outer coordinate, relevance determines both indices of the multiplication label. -/
@[simp]
theorem Term.contributes_z_iff (lam : Term) (i j : Fin 3) :
    lam.Contributes (.z i j) ↔ lam = .P i j := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form, Pi.single_apply, eq_comm]

/-- Relevance has two possibilities: the output is inner, or the label is the private label
selected by that output.
-/
theorem Term.contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ z.IsInner ∨ lam = z.privateTerm := by
  decide +revert

/-- Separate decoding into its two cases: an outer output selects one summand; the inner output
sums the whole label family.
-/
theorem Term.sum_contributes {A : Type*} [AddCommMonoid A] (c : Term → A) (z : OutVar) :
    ∑ lam : Term with lam.Contributes z, c lam
      = match z with
        | .z i j => c (.P i j)
        | .z0 => ∑ lam, c lam := by
  cases z with
  | z i j => simp [filter_eq']
  | z0 => simp

/-- Each output coefficient is the zero-or-one indicator of `Term.Contributes`. -/
theorem chi_eq_ite (lam : Term) (z : OutVar) :
    chi lam z = if lam.Contributes z then 1 else 0 := by
  decide +revert

end Cslib.Algorithms.MatrixMultiplication.Schonhage
