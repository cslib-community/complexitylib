/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.PolyTime.Int.Jet
public import Complexity.Logics.Propositional.CNF.SatisfactionPolynomial
public import Mathlib.Algebra.Order.Ring.Rat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Executable cleared-denominator clause jet evaluation in polynomial time

Executable cleared clause-satisfaction and clause-group product evaluators in `ℤ[z] / (z ^ J)`,
building on `Cslib.mulZJet`, `Cslib.truncZJet`, `Cslib.IntJet`, and
`Cslib.Logic.PL.CNF.clauseSatPoly` / `Cslib.Logic.PL.CNF.cnfSatPoly`, following Appendix B.4
(p. 51) and §2.2 (p. 8) of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH].

## Main definitions and results

* `Cslib.Logic.PL.CNF.evalClauseClearedJet`, `Cslib.Logic.PL.CNF.evalGroupClauseProductJet`.
* `Cslib.Logic.PL.CNF.X_pow_dvd_evalClauseClearedJet`,
  `Cslib.Logic.PL.CNF.X_pow_dvd_evalGroupClauseProductJet`,
  `Cslib.Logic.PL.CNF.X_pow_dvd_evalClauseClearedJet_clauseSatPoly`,
  `Cslib.Logic.PL.CNF.X_pow_dvd_evalGroupClauseProductJet_cnfSatPoly`.
* `Cslib.Logic.PL.CNF.coeffNorm1_evalClauseClearedJet_le`,
  `Cslib.Logic.PL.CNF.coeffNorm1_evalClauseClearedJet_le_pow`,
  `Cslib.Logic.PL.CNF.coeffNorm1_evalGroupClauseProductJet_le`,
  `Cslib.Logic.PL.CNF.coeffNorm1_evalGroupClauseProductJet_le_pow`,
  `Cslib.Logic.PL.CNF.length_encIntBin_getD_evalGroupClauseProductJet_le`.
* `Cslib.Logic.PL.CNF.computableInPolyTime_evalClauseClearedJet`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_evalGroupClauseProductJet`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §2.2 (p. 8), Appendix B.4
  (p. 51).
-/

@[expose] public section

open scoped BigOperators
open Turing.MultiTapeTM

namespace Cslib.Logic.PL.CNF

/-- Cleared clause-satisfaction jet evaluator (Appendix B.4, p. 51 of [OpenAI2026ETH]): computes
`δ ^ litJets.length - ∏_{(pol, X̃) ∈ litJets} (if pol then δ - X̃ else X̃)` modulo `z ^ J` via
`Cslib.mulZJet`, `Cslib.truncZJet`, and `Cslib.IntJet.subConst`.

* **Polarity convention**: each `(pol, X̃)` carries literal polarity `pol : Bool` and cleared
  variable jet `X̃ : List ℤ`; a positive literal (`pol = true`) contributes dissatisfaction factor
  `IntJet.subConst J δ X̃` (`δ - X̃`), and a negative literal (`pol = false`) contributes `X̃`.
* **Totality and shape**: input lists `X̃` may have any length (`getD _ 0` zero-pads missing
  coefficients and truncates degrees `≥ J`), and the output always has exact length `J`.
* **Denominator convention**: total for all `δ : ℤ` (satisfying `X_pow_dvd_evalClauseClearedJet`
  unconditionally, including at `δ = 0`); dividing by `δ` to match `δ ^ |C| * Φ_C(X̃ / δ)` over
  `ℚ[X]` (`X_pow_dvd_evalClauseClearedJet_clauseSatPoly`) requires `δ ≠ 0`. -/
def evalClauseClearedJet (J : ℕ) (δ : ℤ) (litJets : List (Bool × List ℤ)) : List ℤ :=
  IntJet.subConst J (δ ^ litJets.length)
    (litJets.foldl
      (fun acc lit => Cslib.mulZJet J acc (if lit.1 then IntJet.subConst J δ lit.2 else lit.2))
      (Cslib.truncZJet J [1]))

/-- Sequential cleared clause-product jet evaluator (Appendix B.4, p. 51 of [OpenAI2026ETH]):
multiplies the cleared clause jets of `clauses` modulo `z ^ J` via `Cslib.mulZJet` over staged
denominator `δ ^ (∑ |C|)`.

* **Polarity and totality**: inherits the `(pol, X̃)` convention of `evalClauseClearedJet`; input
  literal lists `X̃ : List ℤ` need not have length `J` (`getD _ 0` zero-pads short lists and
  truncates degrees `≥ J`), and the output always has exact length `J` (`Cslib.truncZJet J [1]`
  when `clauses = []`).
* **Denominator convention**: total for all `δ : ℤ` (satisfying
  `X_pow_dvd_evalGroupClauseProductJet` unconditionally, including at `δ = 0`), while the rational
  `δ ^ φ.totalLiterals * Φ_φ(X̃ / δ)` congruence (`X_pow_dvd_evalGroupClauseProductJet_cnfSatPoly`)
  requires `δ ≠ 0`. -/
def evalGroupClauseProductJet (J : ℕ) (δ : ℤ) (clauses : List (List (Bool × List ℤ))) : List ℤ :=
  clauses.foldl (fun acc litJets => Cslib.mulZJet J acc (evalClauseClearedJet J δ litJets))
    (Cslib.truncZJet J [1])

@[simp] theorem length_evalClauseClearedJet (J : ℕ) (δ : ℤ) (litJets : List (Bool × List ℤ)) :
    (evalClauseClearedJet J δ litJets).length = J :=
  IntJet.length_subConst J _ _

@[simp] theorem length_evalGroupClauseProductJet (J : ℕ) (δ : ℤ)
    (clauses : List (List (Bool × List ℤ))) :
    (evalGroupClauseProductJet J δ clauses).length = J :=
  IntJet.length_foldl_mulZJet J (evalClauseClearedJet J δ) clauses (Cslib.length_truncZJet J [1])

/-- **Exact polynomial congruence for `evalClauseClearedJet` modulo `X ^ J`** over `ℤ[X]` (valid
for all `δ : ℤ`, including `δ = 0`). -/
theorem X_pow_dvd_evalClauseClearedJet (J : ℕ) (δ : ℤ) (litJets : List (Bool × List ℤ)) :
    Polynomial.X ^ J ∣
      Polynomial.ofCoeffList (evalClauseClearedJet J δ litJets) -
        (Polynomial.C (δ ^ litJets.length) -
          (litJets.map fun lit => if lit.1 then Polynomial.C δ - Polynomial.ofCoeffList lit.2
            else Polynomial.ofCoeffList lit.2).prod) := by
  unfold evalClauseClearedJet
  set foldOut := litJets.foldl
    (fun acc lit => Cslib.mulZJet J acc (if lit.1 then IntJet.subConst J δ lit.2 else lit.2))
    (Cslib.truncZJet J [1])
  have hfold := IntJet.X_pow_dvd_foldl_mulZJet J litJets
    (fun lit => if lit.1 then IntJet.subConst J δ lit.2 else lit.2)
    (fun lit => if lit.1 then Polynomial.C δ - Polynomial.ofCoeffList lit.2
      else Polynomial.ofCoeffList lit.2)
    (fun lit _ => by
      cases lit.1
      · simp only [Bool.false_eq_true, ↓reduceIte, sub_self, dvd_zero]
      · simp only [↓reduceIte]; exact IntJet.X_pow_dvd_subConst J δ lit.2)
    (Cslib.truncZJet J [1]) 1
    (by simpa only [map_one] using IntJet.X_pow_dvd_truncZJet_singleton J 1)
  rw [one_mul] at hfold
  convert dvd_sub (IntJet.X_pow_dvd_subConst J (δ ^ litJets.length) foldOut) hfold using 1
  ring

/-- **Exact polynomial congruence for `evalGroupClauseProductJet` modulo `X ^ J`** over `ℤ[X]`
(valid for all `δ : ℤ`, including `δ = 0`). -/
theorem X_pow_dvd_evalGroupClauseProductJet (J : ℕ) (δ : ℤ)
    (clauses : List (List (Bool × List ℤ))) :
    Polynomial.X ^ J ∣
      Polynomial.ofCoeffList (evalGroupClauseProductJet J δ clauses) -
        (clauses.map fun litJets => Polynomial.C (δ ^ litJets.length) -
          (litJets.map fun lit => if lit.1 then Polynomial.C δ - Polynomial.ofCoeffList lit.2
            else Polynomial.ofCoeffList lit.2).prod).prod := by
  unfold evalGroupClauseProductJet
  have hfold := IntJet.X_pow_dvd_foldl_mulZJet J clauses (evalClauseClearedJet J δ)
    (fun litJets => Polynomial.C (δ ^ litJets.length) -
      (litJets.map fun lit => if lit.1 then Polynomial.C δ - Polynomial.ofCoeffList lit.2
        else Polynomial.ofCoeffList lit.2).prod)
    (fun litJets _ => X_pow_dvd_evalClauseClearedJet J δ litJets) (Cslib.truncZJet J [1]) 1
    (by simpa only [map_one] using IntJet.X_pow_dvd_truncZJet_singleton J 1)
  rwa [one_mul] at hfold

private theorem X_pow_dvd_map_rat {J : ℕ} {P : Polynomial ℤ} (h : Polynomial.X ^ J ∣ P) :
    (Polynomial.X : Polynomial ℚ) ^ J ∣ P.map (Int.castRingHom ℚ) := by
  simpa only [Polynomial.map_pow, Polynomial.map_X] using
    Polynomial.map_dvd (Int.castRingHom ℚ) h

private theorem cleared_clauseSatPoly_rat_eq {V : Type*} (δ : ℤ) (hδ : δ ≠ 0)
    (varJet : V → List ℤ) (C : Clause V) :
    ((Polynomial.C (δ ^ (C.map fun l => (l.2, varJet l.1)).length) -
        ((C.map fun l => (l.2, varJet l.1)).map fun lit =>
          if lit.1 then Polynomial.C δ - Polynomial.ofCoeffList lit.2
          else Polynomial.ofCoeffList lit.2).prod).map (Int.castRingHom ℚ)) =
      Polynomial.C (δ : ℚ) ^ C.length * MvPolynomial.aeval
        (fun v => (Polynomial.ofCoeffList (varJet v)).map (Int.castRingHom ℚ) *
          Polynomial.C ((δ : ℚ)⁻¹)) (clauseSatPoly ℚ C) := by
  set qJet : V → Polynomial ℚ := fun v =>
    (Polynomial.ofCoeffList (varJet v)).map (Int.castRingHom ℚ) * Polynomial.C ((δ : ℚ)⁻¹)
  have hCinv : (Polynomial.C (δ : ℚ)) * Polynomial.C ((δ : ℚ)⁻¹) = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ (Int.cast_ne_zero.mpr hδ), Polynomial.C_1]
  have hlit (l : Std.Sat.Literal V) :
      (if l.2 then Polynomial.C δ - Polynomial.ofCoeffList (varJet l.1)
        else Polynomial.ofCoeffList (varJet l.1)).map (Int.castRingHom ℚ) =
        Polynomial.C (δ : ℚ) * MvPolynomial.aeval qJet (1 - literalPoly ℚ l) := by
    rcases l with ⟨v, _ | _⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, literalPoly_neg, sub_sub_cancel,
        MvPolynomial.aeval_X, qJet]
      calc _ = (Polynomial.ofCoeffList (varJet v)).map (Int.castRingHom ℚ) *
          (Polynomial.C (δ : ℚ) * Polynomial.C ((δ : ℚ)⁻¹)) := by rw [hCinv, mul_one]
        _ = _ := by ring
    · simp only [↓reduceIte, literalPoly_pos, Polynomial.map_sub, Polynomial.map_C,
        Int.coe_castRingHom, map_sub, map_one, MvPolynomial.aeval_X, qJet]
      calc _ = Polynomial.C (δ : ℚ) * 1 -
          (Polynomial.ofCoeffList (varJet v)).map (Int.castRingHom ℚ) *
            (Polynomial.C (δ : ℚ) * Polynomial.C ((δ : ℚ)⁻¹)) := by rw [mul_one, hCinv, mul_one]
        _ = _ := by ring
  rw [List.length_map, Polynomial.map_sub, Polynomial.map_C, map_pow, Int.coe_castRingHom,
    Polynomial.C_pow, Polynomial.map_list_prod, clauseSatPoly, map_sub, map_one, map_list_prod,
    mul_sub, mul_one]
  congr 1; simp only [List.map_map, Function.comp_def]
  induction C with
  | nil => simp
  | cons l C ih =>
    rw [List.length_cons, pow_succ', List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      ih, hlit l]; ring

/-- **Rational `clauseSatPoly` congruence for `evalClauseClearedJet`**: when `δ ≠ 0`,
`evalClauseClearedJet` on `C` is congruent modulo `X ^ J` over `ℚ[X]` to `δ ^ |C| * Φ_C(X̃ / δ)`. -/
theorem X_pow_dvd_evalClauseClearedJet_clauseSatPoly {V : Type*} (J : ℕ) {δ : ℤ} (hδ : δ ≠ 0)
    (varJet : V → List ℤ) (C : Clause V) :
    (Polynomial.X : Polynomial ℚ) ^ J ∣
      (Polynomial.ofCoeffList (evalClauseClearedJet J δ (C.map fun l => (l.2, varJet l.1)))).map
          (Int.castRingHom ℚ) -
        Polynomial.C (δ : ℚ) ^ C.length * MvPolynomial.aeval
          (fun v => (Polynomial.ofCoeffList (varJet v)).map (Int.castRingHom ℚ) *
            Polynomial.C ((δ : ℚ)⁻¹)) (clauseSatPoly ℚ C) := by
  have hdvd := X_pow_dvd_map_rat
    (X_pow_dvd_evalClauseClearedJet J δ (C.map fun l => (l.2, varJet l.1)))
  rwa [Polynomial.map_sub, cleared_clauseSatPoly_rat_eq δ hδ varJet C] at hdvd

/-- **Rational `cnfSatPoly` congruence for `evalGroupClauseProductJet`**: when `δ ≠ 0`,
`evalGroupClauseProductJet` on `φ` is congruent modulo `X ^ J` over `ℚ[X]` to
`δ ^ φ.totalLiterals * Φ_φ(X̃ / δ)`. -/
theorem X_pow_dvd_evalGroupClauseProductJet_cnfSatPoly {V : Type*} (J : ℕ) {δ : ℤ} (hδ : δ ≠ 0)
    (varJet : V → List ℤ) (φ : CNF V) :
    (Polynomial.X : Polynomial ℚ) ^ J ∣
      (Polynomial.ofCoeffList (evalGroupClauseProductJet J δ
          (φ.map fun C => C.map fun l => (l.2, varJet l.1)))).map (Int.castRingHom ℚ) -
        Polynomial.C (δ : ℚ) ^ φ.totalLiterals * MvPolynomial.aeval
          (fun v => (Polynomial.ofCoeffList (varJet v)).map (Int.castRingHom ℚ) *
            Polynomial.C ((δ : ℚ)⁻¹)) (cnfSatPoly ℚ φ) := by
  have hprod :
      (φ.map fun C : Clause V => Polynomial.map (Int.castRingHom ℚ)
        (Polynomial.C (δ ^ (C.map fun l => (l.2, varJet l.1)).length) -
          ((C.map fun l => (l.2, varJet l.1)).map fun lit =>
            if lit.1 then Polynomial.C δ - Polynomial.ofCoeffList lit.2
            else Polynomial.ofCoeffList lit.2).prod)).prod =
        Polynomial.C (δ : ℚ) ^ φ.totalLiterals * MvPolynomial.aeval
          (fun v => (Polynomial.ofCoeffList (varJet v)).map (Int.castRingHom ℚ) *
            Polynomial.C ((δ : ℚ)⁻¹)) (cnfSatPoly ℚ φ) := by
    induction φ with
    | nil => simp
    | cons C φ ih =>
      rw [List.map_cons, List.prod_cons, ih, totalLiterals_cons, pow_add, cnfSatPoly_cons, map_mul,
        cleared_clauseSatPoly_rat_eq δ hδ varJet C]; ring
  have hdvd := X_pow_dvd_map_rat
    (X_pow_dvd_evalGroupClauseProductJet J δ (φ.map fun C => C.map fun l => (l.2, varJet l.1)))
  rw [Polynomial.map_sub, Polynomial.map_list_prod] at hdvd
  simp only [List.map_map, Function.comp_def] at hprod hdvd
  rwa [hprod] at hdvd

/-- Explicit `ℓ₁` bound on `evalClauseClearedJet` in terms of the literal `ℓ₁` norms. -/
theorem coeffNorm1_evalClauseClearedJet_le (J : ℕ) (δ : ℤ) (litJets : List (Bool × List ℤ)) :
    (Polynomial.ofCoeffList (evalClauseClearedJet J δ litJets)).coeffNorm1 ≤
      2 * (litJets.map fun lit => δ.natAbs + (Polynomial.ofCoeffList lit.2).coeffNorm1).prod := by
  unfold evalClauseClearedJet
  refine (IntJet.coeffNorm1_subConst_le J (δ ^ litJets.length) _).trans ?_
  rw [Int.natAbs_pow, Nat.two_mul]
  have hpow : δ.natAbs ^ litJets.length ≤
      (litJets.map fun lit => δ.natAbs + (Polynomial.ofCoeffList lit.2).coeffNorm1).prod := by
    induction litJets with
    | nil => simp
    | cons _ _ ih =>
      rw [List.length_cons, Nat.pow_succ', List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul (Nat.le_add_right _ _) ih
  have hfold := IntJet.coeffNorm1_foldl_mulZJet_le J litJets
    (fun lit => if lit.1 then IntJet.subConst J δ lit.2 else lit.2)
    (fun lit => δ.natAbs + (Polynomial.ofCoeffList lit.2).coeffNorm1)
    (fun lit _ => by
      cases lit.1
      · exact Nat.le_add_left _ _
      · exact IntJet.coeffNorm1_subConst_le J δ lit.2) (Cslib.truncZJet J [1])
  have h1 : (Polynomial.ofCoeffList (Cslib.truncZJet J [1])).coeffNorm1 ≤ 1 :=
    IntJet.coeffNorm1_truncZJet_singleton_le J 1
  exact Nat.add_le_add hpow
    (hfold.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right _ h1))

/-- Uniform `ℓ₁` bound on `evalClauseClearedJet` when every literal jet has `coeffNorm1 ≤ B`. -/
theorem coeffNorm1_evalClauseClearedJet_le_pow (J : ℕ) (δ : ℤ)
    (litJets : List (Bool × List ℤ)) (B : ℕ)
    (hB : ∀ lit ∈ litJets, (Polynomial.ofCoeffList lit.2).coeffNorm1 ≤ B) :
    (Polynomial.ofCoeffList (evalClauseClearedJet J δ litJets)).coeffNorm1 ≤
      2 * (δ.natAbs + B) ^ litJets.length := by
  refine (coeffNorm1_evalClauseClearedJet_le J δ litJets).trans (Nat.mul_le_mul_left 2 ?_)
  induction litJets with
  | nil => simp
  | cons lit _ ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, Nat.pow_succ']
    exact Nat.mul_le_mul (Nat.add_le_add_left (hB lit List.mem_cons_self) _)
      (ih fun m hm => hB m (List.mem_cons_of_mem _ hm))

/-- Explicit `ℓ₁` bound on `evalGroupClauseProductJet` across all clauses. -/
theorem coeffNorm1_evalGroupClauseProductJet_le (J : ℕ) (δ : ℤ)
    (clauses : List (List (Bool × List ℤ))) :
    (Polynomial.ofCoeffList (evalGroupClauseProductJet J δ clauses)).coeffNorm1 ≤
      (clauses.map fun C =>
        2 * (C.map fun lit => δ.natAbs + (Polynomial.ofCoeffList lit.2).coeffNorm1).prod).prod := by
  unfold evalGroupClauseProductJet
  have h1 : (Polynomial.ofCoeffList (Cslib.truncZJet J [1])).coeffNorm1 ≤ 1 :=
    IntJet.coeffNorm1_truncZJet_singleton_le J 1
  exact (IntJet.coeffNorm1_foldl_mulZJet_le J clauses (evalClauseClearedJet J δ) _
    (fun C _ => coeffNorm1_evalClauseClearedJet_le J δ C) (Cslib.truncZJet J [1])).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right _ h1)

/-- **Appendix B.4 `ℓ₁` norm bound on `evalGroupClauseProductJet`**: if every input literal jet has
`coeffNorm1 ≤ B`, then the product has `coeffNorm1 ≤ 2 ^ |clauses| * (|δ| + B) ^ (∑ |C|)`. -/
theorem coeffNorm1_evalGroupClauseProductJet_le_pow (J : ℕ) (δ : ℤ)
    (clauses : List (List (Bool × List ℤ))) (B : ℕ)
    (hB : ∀ C ∈ clauses, ∀ lit ∈ C, (Polynomial.ofCoeffList lit.2).coeffNorm1 ≤ B) :
    (Polynomial.ofCoeffList (evalGroupClauseProductJet J δ clauses)).coeffNorm1 ≤
      2 ^ clauses.length * (δ.natAbs + B) ^ (clauses.map List.length).sum := by
  unfold evalGroupClauseProductJet
  have h1 : (Polynomial.ofCoeffList (Cslib.truncZJet J [1])).coeffNorm1 ≤ 1 :=
    IntJet.coeffNorm1_truncZJet_singleton_le J 1
  refine (IntJet.coeffNorm1_foldl_mulZJet_le J clauses (evalClauseClearedJet J δ)
    (fun C => 2 * (δ.natAbs + B) ^ C.length)
    (fun C hC => coeffNorm1_evalClauseClearedJet_le_pow J δ C B (hB C hC))
    (Cslib.truncZJet J [1])).trans ?_
  refine (Nat.mul_le_mul_right _ h1).trans ?_
  rw [Nat.one_mul]
  induction clauses with
  | nil => simp
  | cons C cs ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, List.map_cons, List.sum_cons,
      Nat.pow_succ', pow_add]
    exact (Nat.mul_le_mul_left _ (ih fun D hD => hB D (List.mem_cons_of_mem _ hD))).trans_eq
      (by ring)

/-- **Appendix B.4 binary bit-length bound** (applicable to `clauses` and to every prefix
`clauses.take i`): when every literal jet in `clauses` has `coeffNorm1 ≤ B`, every output
coefficient of `evalGroupClauseProductJet J δ clauses` has `encIntBin` bit-length at most
`clauses.length + (clauses.map List.length).sum * (δ.natAbs + B).size + 3`. -/
theorem length_encIntBin_getD_evalGroupClauseProductJet_le (J : ℕ) (δ : ℤ)
    (clauses : List (List (Bool × List ℤ))) (B : ℕ)
    (hB : ∀ C ∈ clauses, ∀ lit ∈ C, (Polynomial.ofCoeffList lit.2).coeffNorm1 ≤ B) (k : ℕ) :
    (encIntBin ((evalGroupClauseProductJet J δ clauses).getD k 0)).length ≤
      clauses.length + (clauses.map List.length).sum * (δ.natAbs + B).size + 3 := by
  refine (IntJet.length_encIntBin_getD_le_coeffNorm1 _ k).trans ?_
  have hsize := (Nat.size_le_size (coeffNorm1_evalGroupClauseProductJet_le_pow J δ clauses B
    hB)).trans (Nat.size_mul_le _ _)
  have h2 : (2 ^ clauses.length).size ≤ clauses.length + 1 :=
    Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))
  have hpow := Nat.size_pow_le (δ.natAbs + B) (clauses.map List.length).sum
  omega

section PolyTime

local notation "encJet" => encList encIntBin
local notation "encLitJet" => encPair encBool (encList encIntBin)
local notation "encClauseJet" => encList (encPair encBool (encList encIntBin))

@[fun_prop] theorem computableInPolyTime_evalClauseClearedJet' {γ : Type} {encIn : γ ↪ List Bool}
    {J : γ → ℕ} {δ : γ → ℤ} {litJets : γ → List (Bool × List ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hδ : ComputableInPolyTime δ encIn encIntBin)
    (hlits : ComputableInPolyTime litJets encIn encClauseJet) :
    ComputableInPolyTime (fun x => evalClauseClearedJet (J x) (δ x) (litJets x)) encIn encJet := by
  unfold evalClauseClearedJet
  have hfold := IntJet.computableInPolyTime_foldl_mulZJet encLitJet
    (fun j d lit => if lit.1 then IntJet.subConst j d lit.2 else lit.2) hJ hδ hlits (by fun_prop)
    (K := fun x => (encIntBin (δ x)).length + 2 * (encClauseJet (litJets x)).length + 2)
    ((hδ.tidy.polyBounded_length.add ((PolyBounded.const 2).mul hlits.tidy.polyBounded_length)).add
      (.const 2))
    (fun x lit hlit => by
      have hδ_sz : (δ x).natAbs.size ≤ (encIntBin (δ x)).length := by rw [length_encIntBin]; omega
      have hlit_enc : (encJet lit.2).length ≤ (encClauseJet (litJets x)).length :=
        (length_le_encPair_right encBool encJet lit).trans (length_le_encList_of_mem encLitJet hlit)
      have hlit_sz := IntJet.size_coeffNorm1_le_length_encList lit.2
      have hle : (Polynomial.ofCoeffList
          (if lit.1 then IntJet.subConst (J x) (δ x) lit.2 else lit.2)).coeffNorm1 ≤
          (δ x).natAbs + (Polynomial.ofCoeffList lit.2).coeffNorm1 := by
        cases lit.1; exacts [Nat.le_add_left _ _, IntJet.coeffNorm1_subConst_le (J x) (δ x) lit.2]
      have hsz := (Nat.size_le_size hle).trans (Nat.size_add_le _ _)
      omega)
  have hpow : ComputableInPolyTime (fun x => (δ x) ^ (litJets x).length) encIn encIntBin :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_pow' hδ.tidy
      ((ComputableTidilyInPolyTime.length_list encLitJet).comp' hlits.tidy))
  exact IntJet.computableInPolyTime_subConst' hJ hpow hfold

theorem computableInPolyTime_evalClauseClearedJet :
    ComputableInPolyTime
      (fun p : (ℕ × ℤ) × List (Bool × List ℤ) => evalClauseClearedJet p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encIntBin) encClauseJet) encJet := by fun_prop

@[fun_prop] theorem computableInPolyTime_evalGroupClauseProductJet' {γ : Type}
    {encIn : γ ↪ List Bool} {J : γ → ℕ} {δ : γ → ℤ}
    {clauses : γ → List (List (Bool × List ℤ))}
    (hJ : ComputableInPolyTime J encIn encUnary) (hδ : ComputableInPolyTime δ encIn encIntBin)
    (hclauses : ComputableInPolyTime clauses encIn (encList encClauseJet)) :
    ComputableInPolyTime (fun x => evalGroupClauseProductJet (J x) (δ x) (clauses x))
      encIn encJet := by
  unfold evalGroupClauseProductJet
  exact IntJet.computableInPolyTime_foldl_mulZJet encClauseJet evalClauseClearedJet
    hJ hδ hclauses (by fun_prop)
    (K := fun x =>
      let M := (encIntBin (δ x)).length + (encList encClauseJet (clauses x)).length
      3 + M * (3 * M + 2))
    ((PolyBounded.const 3).add ((hδ.tidy.polyBounded_length.add
      hclauses.tidy.polyBounded_length).mul (((PolyBounded.const 3).mul
        (hδ.tidy.polyBounded_length.add hclauses.tidy.polyBounded_length)).add (.const 2))))
    (fun x C hC => by
      dsimp only
      set M := (encIntBin (δ x)).length + (encList encClauseJet (clauses x)).length
      have hδ_sz : (δ x).natAbs.size ≤ M := by have h := length_encIntBin (δ x); omega
      have hC_enc : (encClauseJet C).length ≤ M :=
        (length_le_encList_of_mem encClauseJet hC).trans (Nat.le_add_left _ _)
      have hC_len : C.length ≤ M := (length_le_length_encList encLitJet C).trans hC_enc
      have hB : ∀ lit ∈ C, (Polynomial.ofCoeffList lit.2).coeffNorm1 ≤ 2 ^ (2 * M) :=
        fun lit hlit => Nat.le_of_lt (Nat.size_le.mp
          ((IntJet.size_coeffNorm1_le_length_encList lit.2).trans (Nat.mul_le_mul_left 2
            ((length_le_encPair_right encBool encJet lit).trans
              ((length_le_encList_of_mem encLitJet hlit).trans hC_enc)))))
      have h2pow : (2 ^ (2 * M)).size ≤ 2 * M + 1 :=
        Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))
      have hadd_sz : ((δ x).natAbs + 2 ^ (2 * M)).size ≤ 3 * M + 2 :=
        (Nat.size_add_le _ _).trans (by omega)
      have hpow_sz : (((δ x).natAbs + 2 ^ (2 * M)) ^ C.length).size ≤ M * (3 * M + 2) + 1 :=
        (Nat.size_pow_le _ C.length).trans (Nat.add_le_add_right (Nat.mul_le_mul hC_len hadd_sz) 1)
      have h2sz : (2 : ℕ).size ≤ 2 := Nat.size_le.mpr (by omega)
      have hsz := (Nat.size_le_size (coeffNorm1_evalClauseClearedJet_le_pow (J x) (δ x) C
        (2 ^ (2 * M)) hB)).trans (Nat.size_mul_le 2 _)
      omega)

theorem computableInPolyTime_evalGroupClauseProductJet :
    ComputableInPolyTime
      (fun p : (ℕ × ℤ) × List (List (Bool × List ℤ)) =>
        evalGroupClauseProductJet p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encIntBin) (encList encClauseJet)) encJet := by fun_prop

end PolyTime

end Cslib.Logic.PL.CNF
