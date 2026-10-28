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
semantics or running-time statement is imported. Source-derived prose is paraphrased below.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Section 2.2: We call x₁, x₂, x₃, p₁₁, p₁₂, p₂₁, p₂₂ the seven left variables.
-/
inductive LeftVar : Type
  | x (i : Fin 3)
  | p (i j : Fin 2)
  deriving DecidableEq, Fintype

/-- Section 2.2: and y₁, y₂, y₃, q₁₁, q₁₂, q₂₁, q₂₂ the seven right variables.
-/
inductive RightVar : Type
  | y (j : Fin 3)
  | q (i j : Fin 2)
  deriving DecidableEq, Fintype

/-- Section 2.2: We will also use ten output variables z_ij (for 1 ≤ i, j ≤ 3) and z₀.
-/
inductive OutVar : Type
  | z (i j : Fin 3)
  | z0
  deriving DecidableEq, Fintype

/-- Section 2.2: Schönhage's identity has ten terms, which we name P_ij (for 1 ≤ i, j ≤ 3,
corresponding to the entries of p̂ and q̂) and P₀.
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

/-- Section 2.2: the 3 × 3 matrix `p̂` of linear forms, p̂ = (p₁₁, p₁₂, 0; p₂₁, p₂₂, 0; -p₁₁-p₂₁,
-p₁₂-p₂₂, 0).
-/
def pHat : Matrix (Fin 3) (Fin 3) (LeftVar → ℤ) :=
  !![pForm 0 0, pForm 0 1, 0;
     pForm 1 0, pForm 1 1, 0;
     -pForm 0 0 - pForm 1 0, -pForm 0 1 - pForm 1 1, 0]

/-- Section 2.2: the 3 × 3 matrix `q̂` of linear forms, q̂ = (q₁₁, q₁₂, -q₁₁-q₁₂; q₂₁, q₂₂,
-q₂₁-q₂₂; 0, 0, 0).
-/
def qHat : Matrix (Fin 3) (Fin 3) (RightVar → ℤ) :=
  !![qForm 0 0, qForm 0 1, -qForm 0 0 - qForm 0 1;
     qForm 1 0, qForm 1 1, -qForm 1 0 - qForm 1 1;
     0, 0, 0]

/-- Section 2.2: the linear form `φ_λ` in the left variables, φ_{P_ij} = x_i + p̂_ij and φ_{P₀} =
-(x₁ + x₂ + x₃). Section 2.3.1: let φ_λ(s) ∈ {0, ±1} denote the coefficient of s in φ_λ; this is
`phi lam s`.
-/
def phi : Term → LeftVar → ℤ
  | .P i j => xForm i + pHat i j
  | .P0 => -(xForm 0 + xForm 1 + xForm 2)

/-- Section 2.2: the linear form `ψ_λ` in the right variables, ψ_{P_ij} = y_j + q̂_ij and ψ_{P₀} =
y₁ + y₂ + y₃. Section 2.3.1: `ψ_λ(t)`, the coefficient of `t` in `ψ_λ`, is `psi lam t`.
-/
def psi : Term → RightVar → ℤ
  | .P i j => yForm j + qHat i j
  | .P0 => yForm 0 + yForm 1 + yForm 2

/-- Section 2.2: the linear form `χ_λ` in the output variables, χ_{P_ij} = z_ij + z₀ and χ_{P₀} =
z₀.
-/
def chi : Term → OutVar → ℤ
  | .P i j => zForm i j + z0Form
  | .P0 => z0Form

/-- Section 2.2: the output variable `z₀` is inner, the `z_ij` are outer.
-/
def OutVar.IsInner : OutVar → Prop
  | .z _ _ => False
  | .z0 => True

instance OutVar.instDecidablePredIsInner : DecidablePred OutVar.IsInner
  | .z _ _ => isFalse fun h => h
  | .z0 => isTrue trivial

/-- Section 2.2: We say that a term λ contributes to an output variable z if z appears in χ_λ.
-/
def Term.Contributes (lam : Term) (z : OutVar) : Prop := chi lam z ≠ 0

instance Term.instDecidableContributes (lam : Term) (z : OutVar) : Decidable (lam.Contributes z) :=
  inferInstanceAs (Decidable (chi lam z ≠ 0))

/-- The term that the private leaf has at a level where the output string has the variable `z`:
`P₀` for `z₀` and `P_ij` for `z_ij`.
-/
def OutVar.privateTerm : OutVar → Term
  | .z i j => .P i j
  | .z0 => .P0

/-- Section 2.3.1: A left string of length L is a string u = u₁ u₂ ⋯ u_L of L left variables, and
we call u_ℓ its variable at level ℓ.
-/
abbrev LeftStr (L : ℕ) : Type := Fin L → LeftVar
/-- Section 2.3.1: right strings of length `L`.
-/
abbrev RightStr (L : ℕ) : Type := Fin L → RightVar
/-- Section 2.3.1: output strings of length `L`.
-/
abbrev OutStr (L : ℕ) : Type := Fin L → OutVar
/-- Section 2.3.1: We refer to the call reached by choosing the terms τ₁, …, τ_k at levels 1, …, k
as the vertex τ₁ ⋯ τ_k, a string of k terms. It is at depth k.
-/
abbrev Vertex (k : ℕ) : Type := Fin k → Term
/-- Section 2.3.1: the leaves, the vertices τ = τ₁ ⋯ τ_L at depth L.
-/
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

/-- Section 2.2: there are seven left variables.
-/
theorem card_leftVar : Fintype.card LeftVar = 7 := by
  simp [Fintype.card_congr LeftVar.equiv]

/-- Section 2.2: there are seven right variables.
-/
theorem card_rightVar : Fintype.card RightVar = 7 := by
  simp [Fintype.card_congr RightVar.equiv]

/-- Section 2.2: Schönhage's identity has ten terms.
-/
theorem card_term : Fintype.card Term = 10 := by
  simp [Fintype.card_congr Term.equiv]

/-! ### Which terms contribute to which output variables -/

/-- Section 2.2, second observation: every term contributes to z₀.
-/
@[simp]
theorem Term.contributes_z0 (lam : Term) : lam.Contributes .z0 := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form]

/-- Section 2.2, second observation: only P_ij contributes to z_ij.
-/
@[simp]
theorem Term.contributes_z_iff (lam : Term) (i j : Fin 3) :
    lam.Contributes (.z i j) ↔ lam = .P i j := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form, Pi.single_apply, eq_comm]

/-- The second observation in one statement: a term contributes to `z` if and only if `z` is
inner, that is `z₀`, or the term is `z.privateTerm`, which is `P_ij` for `z = z_ij`. (This is the
term that the private leaf of Section 2.4.3 has at a level with the variable `z`.)
-/
theorem Term.contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ z.IsInner ∨ lam = z.privateTerm := by
  decide +revert

/-- A sum over the terms contributing to `z` has the one summand `P_ij` for `z = z_ij`, and runs
over all terms for `z = z₀`. This is how step (4) of the recursions assembles the slice at `z`.
-/
theorem Term.sum_contributes {A : Type*} [AddCommMonoid A] (c : Term → A) (z : OutVar) :
    ∑ lam : Term with lam.Contributes z, c lam
      = match z with
        | .z i j => c (.P i j)
        | .z0 => ∑ lam, c lam := by
  cases z with
  | z i j => simp [filter_eq']
  | z0 => simp

/-- Section 2.2: the χ_λ forms are all sums of output variables (without any minus signs or other
coefficients).
-/
theorem chi_eq_ite (lam : Term) (z : OutVar) :
    chi lam z = if lam.Contributes z then 1 else 0 := by
  decide +revert

end Cslib.Algorithms.MatrixMultiplication.Schonhage
