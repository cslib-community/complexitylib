/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.MultilinearExtension
public import Complexity.Foundations.Data.MvPolynomial.AffineTaylor
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
public import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Clause satisfaction polynomials and univariate replacement counting families

Algebraic encoding of propositional clauses, CNF formulas, and linear-form variable replacements
over an arbitrary commutative ring `R`, following §§2.1–2.3 (equations (2.1)–(2.4), pp. 7–9) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH].

## Main definitions and results

* `Cslib.Logic.PL.CNF.totalLiterals`, `Cslib.Logic.PL.CNF.totalLiterals_le_mul_card`.
* `Cslib.Logic.PL.CNF.literalPoly`, `Cslib.Logic.PL.CNF.clauseSatPoly`,
  `Cslib.Logic.PL.CNF.cnfSatPoly`, `Cslib.Logic.PL.CNF.clauseOccurrenceSatPoly`,
  `Cslib.Logic.PL.CNF.replacementCountPoly`.
* `Cslib.Logic.PL.CNF.eval_one_sub_literalPoly_bitPoint`,
  `Cslib.Logic.PL.CNF.eval_clauseSatPoly_bitPoint`, `Cslib.Logic.PL.CNF.eval_cnfSatPoly_bitPoint`,
  `Cslib.Logic.PL.CNF.sum_eval_cnfSatPoly_eq_modelCountOn`.
* `Cslib.Logic.PL.CNF.totalDegree_clauseSatPoly_le`, `Cslib.Logic.PL.CNF.vars_clauseSatPoly_subset`,
  `Cslib.Logic.PL.CNF.totalDegree_cnfSatPoly_le`,
  `Cslib.Logic.PL.CNF.eval_zero_replacementCountPoly`,
  `Cslib.Logic.PL.CNF.natDegree_replacementCountPoly_le`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§2.1–2.3, pp. 7–9.
-/

@[expose] public section

open scoped BigOperators

namespace Cslib.Logic.PL.CNF

variable {V W : Type*}

/-- Total number of literal occurrences across all clauses of `φ`, `M = ∑_{C ∈ φ} |C|` in equation
(2.1) of [OpenAI2026ETH]. -/
abbrev totalLiterals (φ : CNF V) : ℕ := (φ.map List.length).sum

@[simp] theorem totalLiterals_nil : totalLiterals ([] : CNF V) = 0 := rfl

@[simp] theorem totalLiterals_cons (C : Clause V) (φ : CNF V) :
    totalLiterals (C :: φ) = C.length + totalLiterals φ := by simp [totalLiterals]

/-- `totalLiterals` equals the length of the flattened variable-occurrence list `φ.vars`. -/
theorem totalLiterals_eq_length_vars (φ : CNF V) : φ.totalLiterals = φ.vars.length :=
  (CNF.length_vars φ).symm

/-- Equation (2.1) occurrence bound: if every variable occurring in `φ` belongs to `declared` and
appears at most `k` times in `φ.vars`, then `φ.totalLiterals ≤ k * declared.card`. -/
theorem totalLiterals_le_mul_card [DecidableEq V] {φ : CNF V} {declared : Finset V} {k : ℕ}
    (hvars : φ.vars.toFinset ⊆ declared) (hocc : ∀ v ∈ φ.vars, φ.vars.count v ≤ k) :
    φ.totalLiterals ≤ k * declared.card := by
  rw [totalLiterals_eq_length_vars, ← List.sum_map_count_dedup_eq_length]
  have hsum : (φ.vars.dedup.map fun v => φ.vars.count v).sum ≤ φ.vars.dedup.length * k := by
    refine (List.sum_le_length_nsmul _ k fun n hn => ?_).trans (by simp)
    rcases List.mem_map.mp hn with ⟨v, hv, rfl⟩
    exact hocc v (List.mem_dedup.mp hv)
  have hcard : φ.vars.dedup.length ≤ declared.card := by
    rw [← List.toFinset_card_of_nodup (List.nodup_dedup _)]
    exact Finset.card_le_card fun v hv =>
      hvars (List.mem_toFinset.mpr (List.mem_dedup.mp (List.mem_toFinset.mp hv)))
  exact hsum.trans ((Nat.mul_le_mul_right k hcard).trans (Nat.mul_comm _ _).le)

/-- Satisfaction polynomial of a literal `l = (v, b)`: `X_v` when `b = true` and `1 - X_v` when
`b = false` (§2.2, p. 8 of [OpenAI2026ETH]). -/
noncomputable def literalPoly (R : Type*) [CommRing R] (l : Std.Sat.Literal V) :
    MvPolynomial V R :=
  if l.2 then MvPolynomial.X l.1 else 1 - MvPolynomial.X l.1

@[simp] theorem literalPoly_pos (R : Type*) [CommRing R] (v : V) :
    literalPoly R (v, true) = MvPolynomial.X v := rfl

@[simp] theorem literalPoly_neg (R : Type*) [CommRing R] (v : V) :
    literalPoly R (v, false) = 1 - MvPolynomial.X v := rfl

/-- The dissatisfaction factor `1 - literalPoly R l` is `1 - X_v` (`l.2 = true`) or `X_v`
(`l.2 = false`). -/
theorem one_sub_literalPoly (R : Type*) [CommRing R] (l : Std.Sat.Literal V) :
    1 - literalPoly R l = if l.2 then 1 - MvPolynomial.X l.1 else MvPolynomial.X l.1 := by
  rcases l with ⟨v, _ | _⟩; exacts [sub_sub_cancel 1 _, rfl]

/-- Satisfaction polynomial of a clause `C`: `Φ_C(X) = 1 - ∏_{l ∈ C} (1 - L_l(X))` (§2.2, p. 8 of
[OpenAI2026ETH]). -/
noncomputable def clauseSatPoly (R : Type*) [CommRing R] (C : Clause V) : MvPolynomial V R :=
  1 - (C.map fun l => 1 - literalPoly R l).prod

@[simp] theorem clauseSatPoly_nil (R : Type*) [CommRing R] : clauseSatPoly R ([] : Clause V) = 0 :=
  sub_self 1

/-- Evaluating `literalPoly R l` at `Cslib.BitString.bitPoint x` yields `1` if `l` holds under `x`
and `0` otherwise. -/
theorem eval_literalPoly_bitPoint (R : Type*) [CommRing R] (x : V → Bool) (l : Literal V) :
    MvPolynomial.eval (Cslib.BitString.bitPoint x) (literalPoly R l) =
      if l.eval x then 1 else 0 := by
  rcases l with ⟨v, _ | _⟩ <;> cases h : x v <;>
    simp [literalPoly, Cslib.BitString.bitPoint, Literal.eval, h]

/-- Evaluating `1 - literalPoly R l` at `Cslib.BitString.bitPoint x` yields `0` if `l` holds under
`x` and `1` otherwise. -/
theorem eval_one_sub_literalPoly_bitPoint (R : Type*) [CommRing R] (x : V → Bool)
    (l : Literal V) :
    MvPolynomial.eval (Cslib.BitString.bitPoint x) (1 - literalPoly R l) =
      if l.eval x then 0 else 1 := by
  rw [map_sub, map_one, eval_literalPoly_bitPoint]; cases l.eval x <;> simp

/-- Unconditional Boolean indicator property of `clauseSatPoly`: for every clause `C : Clause V`
(including `[]`, unit clauses, duplicate literals, and tautological clauses), `Φ_C` evaluates on
`Cslib.BitString.bitPoint x` to `1` when `C` is satisfied by `x` and `0` otherwise. -/
theorem eval_clauseSatPoly_bitPoint (R : Type*) [CommRing R] (x : V → Bool) (C : Clause V) :
    MvPolynomial.eval (Cslib.BitString.bitPoint x) (clauseSatPoly R C) =
      if C.eval x then 1 else 0 := by
  suffices hprod : MvPolynomial.eval (Cslib.BitString.bitPoint x)
      ((C.map fun l => 1 - literalPoly R l).prod) = if C.eval x then 0 else 1 by
    rw [clauseSatPoly, map_sub, map_one, hprod]; cases C.eval x <;> simp
  induction C with
  | nil => simp
  | cons l C ih =>
    rw [List.map_cons, List.prod_cons, map_mul, eval_one_sub_literalPoly_bitPoint, ih,
      Clause.eval_cons]
    cases l.eval x <;> cases Clause.eval x C <;> simp

theorem totalDegree_literalPoly_le (R : Type*) [CommRing R] (l : Std.Sat.Literal V) :
    (literalPoly R l).totalDegree ≤ 1 := by
  rcases l with ⟨v, _ | _⟩
  · exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (by simp) (MvPolynomial.totalDegree_X_le v))
  · exact MvPolynomial.totalDegree_X_le v

theorem totalDegree_one_sub_literalPoly_le (R : Type*) [CommRing R] (l : Std.Sat.Literal V) :
    (1 - literalPoly R l).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_literalPoly_le R l))

/-- The total degree of `clauseSatPoly R C` is at most `C.length`. -/
theorem totalDegree_clauseSatPoly_le (R : Type*) [CommRing R] (C : Clause V) :
    (clauseSatPoly R C).totalDegree ≤ C.length := by
  rw [clauseSatPoly]
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) ?_)
  induction C with
  | nil => simp
  | cons l C ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm]
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (totalDegree_one_sub_literalPoly_le R l) ih)

/-- Every variable occurring in `clauseSatPoly R C` belongs to `C.map Prod.fst`. -/
theorem vars_clauseSatPoly_subset {R : Type*} [CommRing R] {C : Clause V} {v : V}
    (hv : v ∈ (clauseSatPoly R C).vars) : v ∈ C.map Prod.fst := by
  classical
  have hx_eq : ∀ {w : V}, v ∈ (MvPolynomial.X w : MvPolynomial V R).vars → v = w :=
    fun {w} hw => by
      by_contra hne
      exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hw) (MvPolynomial.degreeOf_X_of_ne hne)
  unfold clauseSatPoly at hv
  rcases Finset.mem_union.mp (MvPolynomial.vars_sub_subset 1 hv) with h1 | hp
  · rw [MvPolynomial.vars_one] at h1; exact False.elim (Finset.notMem_empty v h1)
  · clear hv
    induction C with
    | nil =>
      rw [List.map_nil, List.prod_nil, MvPolynomial.vars_one] at hp
      exact False.elim (Finset.notMem_empty v hp)
    | cons l D ih =>
      rw [List.map_cons, List.prod_cons] at hp
      rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hp) with hl | hD'
      · rcases l with ⟨w, _ | _⟩
        · rw [literalPoly_neg, sub_sub_cancel] at hl
          rw [List.map_cons, hx_eq hl]; exact List.mem_cons_self
        · rw [literalPoly_pos] at hl
          rcases Finset.mem_union.mp (MvPolynomial.vars_sub_subset 1 hl) with h1 | hx
          · rw [MvPolynomial.vars_one] at h1; exact False.elim (Finset.notMem_empty v h1)
          · rw [List.map_cons, hx_eq hx]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hD')

theorem rename_literalPoly (R : Type*) [CommRing R] (f : V → W) (l : Std.Sat.Literal V) :
    MvPolynomial.rename f (literalPoly R l) = literalPoly R (Prod.map f id l) := by
  rcases l with ⟨v, _ | _⟩ <;> simp [literalPoly, Prod.map]

/-- Renaming variables in `clauseSatPoly` commutes with `Clause.relabel`. -/
theorem rename_clauseSatPoly (R : Type*) [CommRing R] (f : V → W) (C : Clause V) :
    MvPolynomial.rename f (clauseSatPoly R C) = clauseSatPoly R (C.relabel f) := by
  unfold clauseSatPoly Clause.relabel
  rw [map_sub, map_one, map_list_prod]
  simp only [List.map_map, Function.comp_def, map_sub, map_one, rename_literalPoly]

/-- Satisfaction polynomial of a CNF formula `φ`: `∏_{C ∈ φ} Φ_C` (equation (2.2), p. 8 of
[OpenAI2026ETH]). -/
noncomputable def cnfSatPoly (R : Type*) [CommRing R] (φ : CNF V) : MvPolynomial V R :=
  (φ.map (clauseSatPoly R)).prod

@[simp] theorem cnfSatPoly_nil (R : Type*) [CommRing R] : cnfSatPoly R ([] : CNF V) = 1 := rfl

@[simp] theorem cnfSatPoly_cons (R : Type*) [CommRing R] (C : Clause V) (φ : CNF V) :
    cnfSatPoly R (C :: φ) = clauseSatPoly R C * cnfSatPoly R φ := rfl

/-- Renaming variables in `cnfSatPoly` commutes with `CNF.relabel`. -/
theorem rename_cnfSatPoly (R : Type*) [CommRing R] (f : V → W) (φ : CNF V) :
    MvPolynomial.rename f (cnfSatPoly R φ) = cnfSatPoly R (φ.relabel f) := by
  unfold cnfSatPoly CNF.relabel
  rw [map_list_prod]; simp only [List.map_map, Function.comp_def, rename_clauseSatPoly]

/-- Evaluating `cnfSatPoly R φ` at `Cslib.BitString.bitPoint x` yields `1` when `φ` holds under `x`
and `0` otherwise. -/
theorem eval_cnfSatPoly_bitPoint (R : Type*) [CommRing R] (x : V → Bool) (φ : CNF V) :
    MvPolynomial.eval (Cslib.BitString.bitPoint x) (cnfSatPoly R φ) =
      if φ.eval x then 1 else 0 := by
  induction φ with
  | nil => simp
  | cons C φ ih =>
    rw [cnfSatPoly_cons, map_mul, eval_clauseSatPoly_bitPoint, ih, CNF.eval_cons]
    cases C.eval x <;> cases CNF.eval x φ <;> simp

/-- The total degree of `cnfSatPoly R φ` is at most `φ.totalLiterals` (§2.2, p. 8 of
[OpenAI2026ETH]). -/
theorem totalDegree_cnfSatPoly_le (R : Type*) [CommRing R] (φ : CNF V) :
    (cnfSatPoly R φ).totalDegree ≤ φ.totalLiterals := by
  induction φ with
  | nil => simp
  | cons C φ ih =>
    rw [cnfSatPoly_cons, totalLiterals_cons]
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (totalDegree_clauseSatPoly_le R C) ih)

/-- Under `φ.totalLiterals ≤ 3 * n` (equation (2.1)), `(cnfSatPoly R φ).totalDegree ≤ 3 * n`. -/
theorem totalDegree_cnfSatPoly_le_three_mul (R : Type*) [CommRing R] {φ : CNF V} {n : ℕ}
    (hM : φ.totalLiterals ≤ 3 * n) : (cnfSatPoly R φ).totalDegree ≤ 3 * n :=
  (totalDegree_cnfSatPoly_le R φ).trans hM

/-- Every variable occurring in `cnfSatPoly R φ` belongs to `φ.vars`. -/
theorem vars_cnfSatPoly_subset {R : Type*} [CommRing R] {φ : CNF V} {v : V}
    (hv : v ∈ (cnfSatPoly R φ).vars) : v ∈ φ.vars := by
  classical
  induction φ with
  | nil =>
    rw [cnfSatPoly_nil, MvPolynomial.vars_one] at hv
    exact False.elim (Finset.notMem_empty v hv)
  | cons C φ ih =>
    rw [cnfSatPoly_cons] at hv
    simp only [CNF.vars, List.flatten_cons, List.map_append, List.mem_append]
    exact (Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv)).imp vars_clauseSatPoly_subset ih

/-- **Declared-variable polynomial model-count identity** (equation (2.2), p. 8 of
[OpenAI2026ETH]): summing `cnfSatPoly R φ` over all Boolean assignments on `declared` (extended by
`false` outside `declared`) equals `(φ.modelCountOn declared : R)` unconditionally. -/
theorem sum_eval_cnfSatPoly_eq_modelCountOn (R : Type*) [CommRing R] [DecidableEq V]
    (φ : CNF V) (declared : Finset V) :
    (∑ σ : declared → Bool,
      MvPolynomial.eval
        (Cslib.BitString.bitPoint (fun v => if h : v ∈ declared then σ ⟨v, h⟩ else false))
        (cnfSatPoly R φ)) = (φ.modelCountOn declared : R) := by
  simp only [eval_cnfSatPoly_bitPoint, Finset.sum_boole]; rfl

/-- Clause satisfaction polynomial with distinct formal inputs indexed by `Fin C.length`. -/
noncomputable def clauseOccurrenceSatPoly (R : Type*) [CommRing R] (C : Clause V) :
    MvPolynomial (Fin C.length) R :=
  clauseSatPoly R (List.ofFn fun j : Fin C.length => (j, C[j].2))

/-- Renaming each occurrence slot `j : Fin C.length` to `C[j].1` recovers `clauseSatPoly R C`. -/
theorem rename_clauseOccurrenceSatPoly (R : Type*) [CommRing R] (C : Clause V) :
    MvPolynomial.rename (fun j : Fin C.length => C[j].1) (clauseOccurrenceSatPoly R C) =
      clauseSatPoly R C := by
  rw [clauseOccurrenceSatPoly, rename_clauseSatPoly]
  exact congrArg (clauseSatPoly R)
    (List.ext_getElem (by simp [Clause.relabel]) fun i _ _ => by simp [Clause.relabel])

/-- **Univariate replacement counting polynomial** `H(T) ∈ Polynomial R` (equation (2.3), p. 9 of
[OpenAI2026ETH]), defined via `Cslib.AffineTaylor.replacedSum` by substituting for each clause
`e : Fin φ.length` and literal slot `j : Fin φ[e].length` the linear form
`∑_{i ∈ declared} rep e j i * X_i`. -/
noncomputable def replacementCountPoly {R : Type*} [CommRing R]
    (φ : CNF V) (declared : Finset V)
    (rep : ∀ e : Fin φ.length, Fin φ[e].length → V → Polynomial R) : Polynomial R :=
  Cslib.AffineTaylor.replacedSum (Finset.univ : Finset (Fin φ.length))
    (fun e => clauseOccurrenceSatPoly R φ[e]) (fun e j (i : declared) => rep e j i.1)

/-- When `rep` depends only on `(e, v)`, `replacementCountPoly` coincides directly with
`Cslib.AffineTaylor.replacedSum` on `clauseSatPoly R φ[e]`. -/
theorem replacementCountPoly_of_var {R : Type*} [CommRing R]
    (φ : CNF V) (declared : Finset V) (P : Fin φ.length → V → V → Polynomial R) :
    replacementCountPoly φ declared (fun e j => P e φ[e][j].1) =
      Cslib.AffineTaylor.replacedSum (Finset.univ : Finset (Fin φ.length))
        (fun e => clauseSatPoly R φ[e]) (fun e v (i : declared) => P e v i.1) := by
  unfold replacementCountPoly Cslib.AffineTaylor.replacedSum
  refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun e _ => ?_
  dsimp only; rw [← rename_clauseOccurrenceSatPoly R φ[e], MvPolynomial.aeval_rename]; rfl

private theorem sum_eval_zero_rep_eq_bitPoint {R : Type*} [CommRing R] [DecidableEq V]
    {declared : Finset V} (σ : declared → Bool) {p : V → Polynomial R} {v : V}
    (hp : ∀ i ∈ declared, (p i).eval 0 = if i = v then 1 else 0) :
    (∑ i : declared, (p i.1).eval 0 * Cslib.BitString.bitVal R (σ i)) =
      Cslib.BitString.bitPoint (fun w => if h : w ∈ declared then σ ⟨w, h⟩ else false) v := by
  have hterm : ∀ i : declared, (p i.1).eval 0 * Cslib.BitString.bitVal R (σ i) =
      if i.1 = v then Cslib.BitString.bitVal R (σ i) else 0 := fun i => by
    rw [hp i.1 i.2]; split_ifs <;> simp
  simp only [hterm]
  by_cases hv : v ∈ declared
  · rw [Finset.sum_eq_single (⟨v, hv⟩ : declared)
      (fun i _ hne => by simp only [show i.1 ≠ v from fun heq => hne (Subtype.ext heq), ↓reduceIte])
      (fun h => False.elim (h (Finset.mem_univ _)))]
    simp [hv, Cslib.BitString.bitPoint]
  · rw [Finset.sum_eq_zero fun i _ =>
      by simp only [show i.1 ≠ v from fun heq => hv (heq ▸ i.2), ↓reduceIte]]
    simp [hv, Cslib.BitString.bitPoint]

/-- **Restoration at `T = 0`** (first half of equation (2.4), p. 9 of [OpenAI2026ETH]): if every
replacement entry `rep e j i` for `i ∈ declared` evaluates at `0` to `1` when `i = φ[e][j].1` and
`0` otherwise, then `(replacementCountPoly φ declared rep).eval 0 = (φ.modelCountOn declared : R)`
unconditionally. -/
theorem eval_zero_replacementCountPoly {R : Type*} [CommRing R] [DecidableEq V]
    (φ : CNF V) (declared : Finset V)
    (rep : ∀ e : Fin φ.length, Fin φ[e].length → V → Polynomial R)
    (hzero : ∀ (e : Fin φ.length) (j : Fin φ[e].length), ∀ i ∈ declared,
      (rep e j i).eval 0 = if i = φ[e][j].1 then 1 else 0) :
    (replacementCountPoly φ declared rep).eval 0 = (φ.modelCountOn declared : R) := by
  rw [replacementCountPoly, Cslib.AffineTaylor.eval_replacedSum,
    ← sum_eval_cnfSatPoly_eq_modelCountOn R φ declared]
  have huniv : ∀ (inst₁ inst₂ : Fintype (declared → Bool)),
      @Finset.univ _ inst₁ = @Finset.univ _ inst₂ := fun _ _ =>
    Finset.ext fun _ => by simp only [Finset.mem_univ]
  rw [huniv]
  refine Finset.sum_congr rfl fun σ _ => ?_
  let ext : V → R := Cslib.BitString.bitPoint
    (fun v => if h : v ∈ declared then σ ⟨v, h⟩ else false)
  have hprod_eq : (∏ e : Fin φ.length, MvPolynomial.eval ext (clauseSatPoly R φ[e])) =
      MvPolynomial.eval ext (cnfSatPoly R φ) := by
    rw [cnfSatPoly, map_list_prod, ← List.prod_ofFn]
    exact congrArg List.prod (List.ext_getElem (by simp) fun i _ _ => by simp)
  rw [← hprod_eq]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hpt : (fun j : Fin φ[e].length =>
      ∑ i : declared, (rep e j i.1).eval 0 * Cslib.BitString.bitVal R (σ i)) =
      fun j : Fin φ[e].length => ext φ[e][j].1 :=
    funext fun j => sum_eval_zero_rep_eq_bitPoint σ (hzero e j)
  rw [hpt, ← Function.comp_def ext (fun j : Fin φ[e].length => φ[e][j].1),
    ← MvPolynomial.eval_rename, rename_clauseOccurrenceSatPoly]

private theorem natDegree_aeval_clauseSatPoly_le {R : Type*} [CommRing R] {κ : Type*}
    (C : Clause κ) (g : κ → Polynomial R) (R_deg : ℕ)
    (hg : ∀ l ∈ C, (g l.1).natDegree ≤ R_deg) :
    (MvPolynomial.aeval g (clauseSatPoly R C)).natDegree ≤ C.length * R_deg := by
  rw [clauseSatPoly, map_sub, map_one]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  rw [map_list_prod]
  induction C with
  | nil => simp
  | cons l C ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    have hl_deg : (MvPolynomial.aeval g (1 - literalPoly R l)).natDegree ≤ R_deg := by
      rw [one_sub_literalPoly]
      rcases l with ⟨v, _ | _⟩
      · simpa only [Bool.false_eq_true, ↓reduceIte, MvPolynomial.aeval_X] using
          hg (v, false) List.mem_cons_self
      · simp only [↓reduceIte, map_sub, map_one, MvPolynomial.aeval_X]
        exact (Polynomial.natDegree_sub_le _ _).trans
          (max_le (by simp) (hg (v, true) List.mem_cons_self))
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hl_deg (ih fun m hm => hg m (List.mem_cons_of_mem _ hm)))

/-- **Degree bound on `replacementCountPoly`** (second half of equation (2.4), p. 9 of
[OpenAI2026ETH]): if every replacement entry `rep e j i` for `i ∈ declared` has univariate degree at
most `R_deg`, then `(replacementCountPoly φ declared rep).natDegree ≤ φ.totalLiterals * R_deg`. -/
theorem natDegree_replacementCountPoly_le {R : Type*} [CommRing R]
    (φ : CNF V) (declared : Finset V)
    (rep : ∀ e : Fin φ.length, Fin φ[e].length → V → Polynomial R) (R_deg : ℕ)
    (hdeg : ∀ (e : Fin φ.length) (j : Fin φ[e].length), ∀ i ∈ declared,
      (rep e j i).natDegree ≤ R_deg) :
    (replacementCountPoly φ declared rep).natDegree ≤ φ.totalLiterals * R_deg := by
  classical
  rw [replacementCountPoly, Cslib.AffineTaylor.replacedSum]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
  have hlen_sum : (∑ e : Fin φ.length, φ[e].length) = φ.totalLiterals := by
    rw [totalLiterals, ← List.sum_ofFn]
    exact congrArg List.sum (List.ext_getElem (by simp) fun i _ _ => by simp)
  calc
    (∏ e : Fin φ.length, MvPolynomial.aeval
        (fun j => ∑ i : declared, rep e j i.1 * Polynomial.C (Cslib.BitString.bitVal R (σ i)))
        (clauseOccurrenceSatPoly R φ[e])).natDegree ≤
        ∑ e : Fin φ.length, φ[e].length * R_deg := by
      refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
      rw [clauseOccurrenceSatPoly]
      refine (natDegree_aeval_clauseSatPoly_le _ _ R_deg fun l _ => ?_).trans
        (by rw [List.length_ofFn])
      exact (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun i _ =>
        (Polynomial.natDegree_mul_C_le _ _).trans (hdeg e l.1 i.1 i.2))
    _ = φ.totalLiterals * R_deg := by rw [← Finset.sum_mul, hlen_sum]

/-- Under `φ.totalLiterals ≤ 3 * declared.card` (equation (2.1)), `replacementCountPoly` has degree
at most `3 * declared.card * R_deg` (equation (2.4) of [OpenAI2026ETH]). -/
theorem natDegree_replacementCountPoly_le_three_mul {R : Type*} [CommRing R]
    (φ : CNF V) (declared : Finset V)
    (rep : ∀ e : Fin φ.length, Fin φ[e].length → V → Polynomial R) (R_deg : ℕ)
    (hM : φ.totalLiterals ≤ 3 * declared.card)
    (hdeg : ∀ (e : Fin φ.length) (j : Fin φ[e].length), ∀ i ∈ declared,
      (rep e j i).natDegree ≤ R_deg) :
    (replacementCountPoly φ declared rep).natDegree ≤ 3 * declared.card * R_deg :=
  (natDegree_replacementCountPoly_le φ declared rep R_deg hdeg).trans
    (Nat.mul_le_mul_right R_deg hM)

end Cslib.Logic.PL.CNF
