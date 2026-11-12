/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Communication.DenseRestriction
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Block
import Mathlib.Tactic

/-!
# Protocols for dense restrictions as formulas with auxiliary variables

[ChukhinKulikovMihajlinSmal2026], Lemma 6.1 (printed p. 13; PDF p. 14) extends the
Karchmer–Wigderson correspondence to the restricted composition `R_g(X)` (`composeKW`). A
protocol of depth `d` solving `R_g(X)` on `X × X` gives a De Morgan formula `φ(Z, p)` of depth at
most `d`. It reads the `m × n` matrix variables `Z` and one auxiliary variable `p_c` for each
`c ∈ {0, 1}ᵐ`, and on every `Z ∈ X` it equals `p_{gᵐ(Z)}` for every assignment `p`
(`exists_auxFormula`). The auxiliary variables occur only positively, so `φ` is monotone in `p`
(`auxFormula_monotone`).

The formula is built like `Protocol.kwFormula`, by recursion on the protocol along the rectangle
`A × B` that reaches each node. Alice's nodes become AND gates and Bob's become OR gates. An
answer leaf `(i, j)` becomes the literal of `Z_{i,j}` that is false on `A` and true on `B`, and a
reject leaf becomes `p_c` for the common value `c` of `gᵐ` there. By induction,
`φ(Z, p) ≤ p_{gᵐ(Z)}` on `A` and `φ(Z, p) ≥ p_{gᵐ(Z)}` on `B`. The source first removes nodes
with an empty rectangle; the recursion here uses constants at such leaves instead.

Inputs are laid out as the `m * n` matrix bits followed by the `2 ^ m` auxiliary bits
(`auxInput`): `Z_{i,j}` is bit `finProdFinEquiv (i, j)` and `p_c` is bit
`m * n + BitString.equivFin c`.

The predictor `τ_φ` of Section 6.3 (`predictor`) reads off the row values that a formula
determines. The formula of a protocol for `R_g(X)` predicts `gᵐ` correctly on `X`
(`predictor_auxFormula`). This is the bridge to the union bound over formulas in Lemmas 6.4–6.5,
which, like Lemmas 6.2–6.3 and Theorem 6.6, are not formalized yet.

## Main definitions

* `Cslib.Circuits.Boolean.auxInput`: a matrix and an assignment to the auxiliary variables as
  one input.
* `Cslib.Circuits.Boolean.auxFormula`: the formula of a protocol for `R_g(X)`.
* `Cslib.Circuits.Boolean.predictor`: the predictor `τ_φ` of a formula.

## Main results

* `Cslib.Circuits.Boolean.exists_auxFormula`: Lemma 6.1.
* `Cslib.Circuits.Boolean.predictor_auxFormula`: the predictor of a protocol's formula is
  correct on `X`.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
-/

public section

namespace Cslib.Circuits.Boolean

open Cslib.Communication Cslib.BitString Formula

variable {m n : ℕ}

/-- The row values `gᵐ(Z) = (g(Z₁), …, g(Zₘ))` of a matrix. -/
@[expose] def rowValues (g : BitString n → Bool) (Z : Fin m → BitString n) : BitString m :=
  fun i => g (Z i)

/-- A matrix `Z` and an assignment `p` to the auxiliary variables, as one input of `m * n + 2 ^ m`
bits: the matrix bits in `BitString.block` order, then `p_c` at `m * n + BitString.equivFin c`. -/
@[expose] def auxInput (Z : Fin m → BitString n) (p : BitString m → Bool) :
    BitString (m * n + 2 ^ m) :=
  Fin.append (blocksEquiv.symm Z) (p ∘ (equivFin m).symm)

/-- The variable `Z_{i,j}`. -/
@[expose] def matrixVar (i : Fin m) (j : Fin n) : Fin (m * n + 2 ^ m) :=
  Fin.castAdd (2 ^ m) (finProdFinEquiv (i, j))

/-- The auxiliary variable `p_c`. -/
@[expose] def auxVar (c : BitString m) : Fin (m * n + 2 ^ m) :=
  Fin.natAdd (m * n) (equivFin m c)

@[simp] theorem auxInput_matrixVar (Z : Fin m → BitString n) (p : BitString m → Bool) (i : Fin m)
    (j : Fin n) : auxInput Z p (matrixVar i j) = Z i j := by
  simp [auxInput, matrixVar]

@[simp] theorem auxInput_auxVar (Z : Fin m → BitString n) (p : BitString m → Bool)
    (c : BitString m) : auxInput Z p (auxVar (n := n) c) = p c := by
  simp [auxInput, auxVar]

open Classical in
/-- **The formula of a protocol for `R_g(X)`** on the rectangle `A × B`. Alice's nodes become AND
gates and Bob's become OR gates. An answer leaf `(i, j)` becomes the literal of `Z_{i,j}` that is
false on `A` and true on `B`. A reject leaf becomes the auxiliary variable `p_c` for the common
value `c` of `gᵐ` on `A ∪ B`. When a side is empty, a leaf becomes a constant. -/
noncomputable def auxFormula (g : BitString n → Bool) :
    Protocol (Fin m → BitString n) (Fin m → BitString n) (Option (Fin m × Fin n)) →
      Set (Fin m → BitString n) → Set (Fin m → BitString n) → Formula signature (m * n + 2 ^ m)
  | .output a, A, B =>
    if hA : A.Nonempty then
      if B.Nonempty then
        match a with
        | some (i, j) =>
          if ∃ Z ∈ A, Z i j = true then (Formula.input (matrixVar i j)).not
          else .input (matrixVar i j)
        | none => .input (auxVar (rowValues g hA.some))
      else .const false
    else .const true
  | .alice send p₀ p₁, A, B =>
    (auxFormula g p₀ {Z ∈ A | send Z = false} B).and (auxFormula g p₁ {Z ∈ A | send Z = true} B)
  | .bob send p₀ p₁, A, B =>
    (auxFormula g p₀ A {Z ∈ B | send Z = false}).or (auxFormula g p₁ A {Z ∈ B | send Z = true})

/-- The formula of a protocol has at most as many AND and OR gates on a path as the protocol
sends bits. -/
theorem depthWith_auxFormula_le (g : BitString n → Bool)
    (p : Protocol (Fin m → BitString n) (Fin m → BitString n) (Option (Fin m × Fin n)))
    (A B : Set (Fin m → BitString n)) : (auxFormula g p A B).depthWith binaryCost ≤ p.depth := by
  induction p generalizing A B with
  | output a =>
    simp only [auxFormula]
    split_ifs <;> [(split <;> [split_ifs <;> simp; simp]); simp; simp]
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [auxFormula, depthWith_and, binaryCost_and, Protocol.depth_alice]
    exact Nat.add_le_add_right (max_le_max (ih₀ _ _) (ih₁ _ _)) 1
  | bob send p₀ p₁ ih₀ ih₁ =>
    rw [auxFormula, depthWith_or, binaryCost_or, Protocol.depth_bob]
    exact Nat.add_le_add_right (max_le_max (ih₀ _ _) (ih₁ _ _)) 1

/-- The formula of a protocol is monotone in the auxiliary variables: they occur only
positively. -/
theorem auxFormula_monotone (g : BitString n → Bool)
    (p : Protocol (Fin m → BitString n) (Fin m → BitString n) (Option (Fin m × Fin n)))
    (A B : Set (Fin m → BitString n)) (Z : Fin m → BitString n) :
    Monotone fun q : BitString m → Bool =>
      (auxFormula g p A B).eval interpretation (auxInput Z q) := by
  induction p generalizing A B with
  | output a =>
    intro q q' hqq'
    simp only [auxFormula]
    split_ifs
    · split
      · split_ifs <;> simp
      · simpa using hqq' _
    · simp
    · simp
  | alice send p₀ p₁ ih₀ ih₁ =>
    intro q q' hqq'
    simp only [auxFormula, eval_and]
    have h₀ := ih₀ {Z ∈ A | send Z = false} B hqq'
    have h₁ := ih₁ {Z ∈ A | send Z = true} B hqq'
    simp only [Bool.le_iff_imp, Bool.and_eq_true] at h₀ h₁ ⊢
    tauto
  | bob send p₀ p₁ ih₀ ih₁ =>
    intro q q' hqq'
    simp only [auxFormula, eval_or]
    have h₀ := ih₀ A {Z ∈ B | send Z = false} hqq'
    have h₁ := ih₁ A {Z ∈ B | send Z = true} hqq'
    simp only [Bool.le_iff_imp, Bool.or_eq_true] at h₀ h₁ ⊢
    tauto

/-- **The invariant of Lemma 6.1.** If `p` solves `R_g` on `A × B`, then its formula is at most
`q_{gᵐ(Z)}` on `A` and at least `q_{gᵐ(Z)}` on `B`, for every assignment `q`. -/
theorem eval_auxFormula {g : BitString n → Bool}
    {p : Protocol (Fin m → BitString n) (Fin m → BitString n) (Option (Fin m × Fin n))}
    {A B : Set (Fin m → BitString n)} (hp : p.Solves (composeKW g) A B)
    (q : BitString m → Bool) :
    (∀ Z ∈ A, (auxFormula g p A B).eval interpretation (auxInput Z q) ≤ q (rowValues g Z)) ∧
      ∀ Z ∈ B, q (rowValues g Z) ≤ (auxFormula g p A B).eval interpretation (auxInput Z q) := by
  induction p generalizing A B with
  | output a =>
    have hs : ∀ x ∈ A, ∀ y ∈ B, composeKW g x y a := fun x hx y hy => hp x hx y hy
    by_cases hA : A.Nonempty
    · have hAn := hA
      by_cases hB : B.Nonempty
      · have hBn := hB
        obtain ⟨y₀, hy₀⟩ := hB
        cases a with
        | some c =>
          obtain ⟨i, j⟩ := c
          have hne : ∀ x ∈ A, ∀ y ∈ B, x i j ≠ y i j := fun x hx y hy => hs x hx y hy
          by_cases hex : ∃ Z ∈ A, Z i j = true
          · obtain ⟨x₁, hx₁, hx₁t⟩ := hex
            have hB' : ∀ y ∈ B, y i j = false := fun y hy => by
              simpa [hx₁t] using (hne x₁ hx₁ y hy).symm
            have hA' : ∀ x ∈ A, x i j = true := fun x hx => by
              simpa [hB' y₀ hy₀] using hne x hx y₀ hy₀
            have hex : ∃ Z ∈ A, Z i j = true := ⟨x₁, hx₁, hx₁t⟩
            simp only [auxFormula, hAn, hBn, hex, ↓reduceDIte, ↓reduceIte]
            refine ⟨fun Z hZ => by simp [hA' Z hZ], fun Z hZ => by simp [hB' Z hZ]⟩
          · push Not at hex
            have hA' : ∀ x ∈ A, x i j = false := fun x hx => by simpa using hex x hx
            obtain ⟨x₀, hx₀⟩ := hA
            have hB' : ∀ y ∈ B, y i j = true := fun y hy => by
              simpa [hA' x₀ hx₀] using (hne x₀ hx₀ y hy).symm
            have hex' : ¬ ∃ Z ∈ A, Z i j = true := by simpa using hex
            simp only [auxFormula, hAn, hBn, hex', ↓reduceDIte, ↓reduceIte]
            refine ⟨fun Z hZ => by simp [hA' Z hZ], fun Z hZ => by simp [hB' Z hZ]⟩
        | none =>
          have hrow : ∀ x ∈ A, ∀ y ∈ B, rowValues g x = rowValues g y := fun x hx y hy =>
            funext (hs x hx y hy)
          have hc (Z) (hZ : Z ∈ A ∪ B) : rowValues g hA.some = rowValues g Z := by
            rcases hZ with hZ | hZ
            · rw [hrow _ hA.some_mem y₀ hy₀, hrow Z hZ y₀ hy₀]
            · exact hrow _ hA.some_mem Z hZ
          simp only [auxFormula, hAn, hBn, ↓reduceDIte, ↓reduceIte, eval_input, auxInput_auxVar]
          exact ⟨fun Z hZ => (congrArg q (hc Z (.inl hZ))).le,
            fun Z hZ => (congrArg q (hc Z (.inr hZ))).ge⟩
      · rw [Set.not_nonempty_iff_eq_empty] at hB
        simp only [auxFormula, hA, dite_true, hB, Set.not_nonempty_empty, ite_false, eval_const]
        exact ⟨fun _ _ => Bool.false_le _, fun _ h => h.elim⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hA
      simp only [auxFormula, hA, Set.not_nonempty_empty, dite_false, eval_const]
      exact ⟨fun _ h => h.elim, fun _ _ => Bool.le_true _⟩
  | alice send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀ (A := {Z ∈ A | send Z = false}) (B := B) fun x hx y hy => by
      simpa [hx.2] using hp x hx.1 y hy
    have h₁ := ih₁ (A := {Z ∈ A | send Z = true}) (B := B) fun x hx y hy => by
      simpa [hx.2] using hp x hx.1 y hy
    simp only [auxFormula, eval_and]
    refine ⟨fun Z hZ => ?_, fun Z hZ => ?_⟩
    · cases h : send Z
      · have := h₀.1 Z ⟨hZ, h⟩
        simp only [Bool.le_iff_imp, Bool.and_eq_true] at this ⊢
        tauto
      · have := h₁.1 Z ⟨hZ, h⟩
        simp only [Bool.le_iff_imp, Bool.and_eq_true] at this ⊢
        tauto
    · have := h₀.2 Z hZ
      have := h₁.2 Z hZ
      simp only [Bool.le_iff_imp, Bool.and_eq_true] at *
      tauto
  | bob send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀ (A := A) (B := {Z ∈ B | send Z = false}) fun x hx y hy => by
      simpa [hy.2] using hp x hx y hy.1
    have h₁ := ih₁ (A := A) (B := {Z ∈ B | send Z = true}) fun x hx y hy => by
      simpa [hy.2] using hp x hx y hy.1
    simp only [auxFormula, eval_or]
    refine ⟨fun Z hZ => ?_, fun Z hZ => ?_⟩
    · have := h₀.1 Z hZ
      have := h₁.1 Z hZ
      simp only [Bool.le_iff_imp, Bool.or_eq_true] at *
      tauto
    · cases h : send Z
      · have := h₀.2 Z ⟨hZ, h⟩
        simp only [Bool.le_iff_imp, Bool.or_eq_true] at this ⊢
        tauto
      · have := h₁.2 Z ⟨hZ, h⟩
        simp only [Bool.le_iff_imp, Bool.or_eq_true] at this ⊢
        tauto

/-- **[ChukhinKulikovMihajlinSmal2026], Lemma 6.1.** A protocol of depth `d` solving `R_g(X)`
gives a De Morgan formula `φ(Z, p)` of `binaryCost` depth at most `d`, monotone in the auxiliary
variables, with `φ(Z, p) = p_{gᵐ(Z)}` for every `Z ∈ X` and every assignment `p`. -/
theorem exists_auxFormula {g : BitString n → Bool} {X : Set (Fin m → BitString n)}
    {p : Protocol (Fin m → BitString n) (Fin m → BitString n) (Option (Fin m × Fin n))}
    (hp : p.Solves (composeKW g) X X) :
    ∃ φ : Formula signature (m * n + 2 ^ m), φ.depthWith binaryCost ≤ p.depth ∧
      (∀ Z, Monotone fun q : BitString m → Bool => φ.eval interpretation (auxInput Z q)) ∧
      ∀ Z ∈ X, ∀ q : BitString m → Bool,
        φ.eval interpretation (auxInput Z q) = q (rowValues g Z) :=
  ⟨auxFormula g p X X, depthWith_auxFormula_le g p X X, auxFormula_monotone g p X X,
    fun Z hZ q => le_antisymm ((eval_auxFormula hp q).1 Z hZ) ((eval_auxFormula hp q).2 Z hZ)⟩

open Classical in
/-- **The predictor of a formula** ([ChukhinKulikovMihajlinSmal2026], Section 6.3, printed
p. 16): `τ_φ(Z) = some c` when `φ(Z, p) = p_c` for every assignment `p`, and `none` (the
source's `⊥`) otherwise. Distinct `c` give distinct functions of `p` (`predictor_eq_some_iff`),
so the predictor is well defined for every formula, not only for those of Lemma 6.1. -/
noncomputable def predictor (φ : Formula signature (m * n + 2 ^ m)) (Z : Fin m → BitString n) :
    Option (BitString m) :=
  if h : ∃ c : BitString m, ∀ q : BitString m → Bool, φ.eval interpretation (auxInput Z q) = q c
  then some h.choose else none

/-- `τ_φ(Z) = c` exactly when `φ(Z, p) = p_c` for every assignment `p`. -/
theorem predictor_eq_some_iff {φ : Formula signature (m * n + 2 ^ m)} {Z : Fin m → BitString n}
    {c : BitString m} :
    predictor φ Z = some c ↔
      ∀ q : BitString m → Bool, φ.eval interpretation (auxInput Z q) = q c := by
  classical
  have huniq (c c' : BitString m)
      (hc : ∀ q : BitString m → Bool, φ.eval interpretation (auxInput Z q) = q c)
      (hc' : ∀ q : BitString m → Bool, φ.eval interpretation (auxInput Z q) = q c') : c = c' := by
    have := (hc fun x => decide (x = c)).symm.trans (hc' fun x => decide (x = c))
    simpa [eq_comm] using this
  unfold predictor
  split_ifs with h
  · refine ⟨fun hs => ?_, fun hc => ?_⟩
    · rw [← Option.some_injective _ hs]
      exact h.choose_spec
    · rw [huniq _ _ h.choose_spec hc]
  · simp only [false_iff]
    exact fun hc => h ⟨c, hc⟩

/-- The formula of Lemma 6.1 predicts `gᵐ` correctly on `X`: `τ_φ(Z) = gᵐ(Z)` for `Z ∈ X`. -/
theorem predictor_auxFormula {g : BitString n → Bool} {X : Set (Fin m → BitString n)}
    {p : Protocol (Fin m → BitString n) (Fin m → BitString n) (Option (Fin m × Fin n))}
    (hp : p.Solves (composeKW g) X X) {Z : Fin m → BitString n} (hZ : Z ∈ X) :
    predictor (auxFormula g p X X) Z = some (rowValues g Z) :=
  predictor_eq_some_iff.2 fun q =>
    le_antisymm ((eval_auxFormula hp q).1 Z hZ) ((eval_auxFormula hp q).2 Z hZ)

end Cslib.Circuits.Boolean
