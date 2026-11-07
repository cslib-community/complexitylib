/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cutting planes

The *cutting planes* proof system [Cook, Coullard and Turán][CookCoullardTuran1987] reasons about
integer linear inequalities `∑ᵥ aᵥ xᵥ ≥ b` over variables ranging over `{0, 1}`
(`Cslib.Logic.PL.Ineq`, with finitely supported integer coefficients). A line follows from earlier
lines by

* adding two lines,
* multiplying a line by a positive integer, or
* **rounded division** [Chvátal][Chvatal1973]: from `∑ᵥ (c aᵥ) xᵥ ≥ b` with `c > 0` infer
  `∑ᵥ aᵥ xᵥ ≥ ⌈b / c⌉` (`Cslib.Logic.PL.Ineq.div`),

and the axioms are `xᵥ ≥ 0` and `-xᵥ ≥ -1`. Rounding is sound because the left-hand side takes
integer values on integer points. These are the rules of [Krajíček, Section 1][Krajicek1997] and
[Jukna, Section 19.1][Jukna2012]. A *cutting planes proof* from a set `Γ` of inequalities
(`Cslib.Logic.PL.CuttingPlanes.IsProof`) is a list of inequalities, from its last line to its first,
each of which is in `Γ`, an axiom, or follows from earlier lines by a rule. Its *size* is its number
of lines and a *refutation* is a proof with the contradiction `0 ≥ 1` (`Cslib.Logic.PL.Ineq.contra`)
among its lines. Coefficient sizes are not measured.

Every line of a proof from `Γ` holds under every 0/1 assignment satisfying `Γ`
(`Cslib.Logic.PL.CuttingPlanes.IsProof.holds`), so a refutable system has no 0/1 solution.

A clause `C` translates to `∑_{v ∈ C} xᵥ + ∑_{¬v ∈ C} (1 - xᵥ) ≥ 1` over its distinct literals
(`Cslib.Logic.PL.Clause.toIneq`), which holds under an assignment exactly when the clause does
(`Cslib.Logic.PL.Clause.holds_toIneq_iff`) [Jukna, Section 19.2][Jukna2012]. A CNF `φ` gives the
system `φ.toIneqs` of the inequalities of its clauses, which cutting planes refute only if `φ` is
unsatisfiable.

## Main definitions

* `Cslib.Logic.PL.Ineq`: integer linear inequalities, with `Cslib.Logic.PL.Ineq.Holds` their
  satisfaction by 0/1 assignments.
* `Cslib.Logic.PL.Ineq.contra`, `Cslib.Logic.PL.Ineq.nonneg`, `Cslib.Logic.PL.Ineq.leOne`: the
  contradiction `0 ≥ 1` and the axioms `xᵥ ≥ 0` and `-xᵥ ≥ -1`.
* `Cslib.Logic.PL.Ineq.div`: rounded division.
* `Cslib.Logic.PL.Literal.toIneq`, `Cslib.Logic.PL.Clause.toIneq`, `Cslib.Logic.PL.CNF.toIneqs`:
  literals, clauses and CNFs as inequalities.
* `Cslib.Logic.PL.CuttingPlanes.IsProof`: cutting planes proofs.
* `Cslib.Logic.PL.CuttingPlanes.DerivableInSize`, `Cslib.Logic.PL.CuttingPlanes.RefutableInSize`:
  derivability and refutability with a bounded number of lines.

## Main results

* `Cslib.Logic.PL.Ineq.Holds.div`: soundness of rounded division.
* `Cslib.Logic.PL.Clause.holds_toIneq_iff`: the translation of clauses is faithful.
* `Cslib.Logic.PL.CuttingPlanes.IsProof.holds`,
  `Cslib.Logic.PL.CuttingPlanes.RefutableInSize.not_exists_holds`,
  `Cslib.Logic.PL.CuttingPlanes.RefutableInSize.not_satisfiable`: soundness.
* `Cslib.Logic.PL.CuttingPlanes.IsProof.comp`,
  `Cslib.Logic.PL.CuttingPlanes.DerivableInSize.extend`: composing proofs.

## References

* [V. Chvátal, *Edmonds polytopes and a hierarchy of combinatorial problems*][Chvatal1973]
* [W. Cook, C. R. Coullard, Gy. Turán, *On the complexity of cutting-plane
  proofs*][CookCoullardTuran1987]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Sections 19.1 and
  19.2][Jukna2012]
* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*, Section 1][Krajicek1997]
-/

public section

open Finset

namespace Cslib.Logic.PL

noncomputable section

/-- An **integer linear inequality** `∑ᵥ aᵥ xᵥ ≥ b` over the variables `V`, with finitely many
nonzero coefficients. Inequalities form an additive group under coefficientwise operations. -/
@[ext]
structure Ineq (V : Type*) where
  /-- The coefficients `aᵥ`. -/
  coeff : V →₀ ℤ
  /-- The bound `b`. -/
  bound : ℤ

namespace Ineq

variable {V : Type*}

instance : Zero (Ineq V) := ⟨⟨0, 0⟩⟩
instance : Add (Ineq V) := ⟨fun I J => ⟨I.coeff + J.coeff, I.bound + J.bound⟩⟩
instance : Neg (Ineq V) := ⟨fun I => ⟨-I.coeff, -I.bound⟩⟩
instance : Sub (Ineq V) := ⟨fun I J => ⟨I.coeff - J.coeff, I.bound - J.bound⟩⟩
instance : SMul ℕ (Ineq V) := ⟨fun c I => ⟨c • I.coeff, c • I.bound⟩⟩
instance : SMul ℤ (Ineq V) := ⟨fun c I => ⟨c • I.coeff, c • I.bound⟩⟩

@[simp] theorem coeff_zero : (0 : Ineq V).coeff = 0 := rfl
@[simp] theorem bound_zero : (0 : Ineq V).bound = 0 := rfl
@[simp] theorem coeff_add (I J : Ineq V) : (I + J).coeff = I.coeff + J.coeff := rfl
@[simp] theorem bound_add (I J : Ineq V) : (I + J).bound = I.bound + J.bound := rfl
@[simp] theorem coeff_neg (I : Ineq V) : (-I).coeff = -I.coeff := rfl
@[simp] theorem bound_neg (I : Ineq V) : (-I).bound = -I.bound := rfl
@[simp] theorem coeff_sub (I J : Ineq V) : (I - J).coeff = I.coeff - J.coeff := rfl
@[simp] theorem bound_sub (I J : Ineq V) : (I - J).bound = I.bound - J.bound := rfl
@[simp] theorem coeff_nsmul (c : ℕ) (I : Ineq V) : (c • I).coeff = c • I.coeff := rfl
@[simp] theorem bound_nsmul (c : ℕ) (I : Ineq V) : (c • I).bound = c • I.bound := rfl
@[simp] theorem coeff_zsmul (c : ℤ) (I : Ineq V) : (c • I).coeff = c • I.coeff := rfl
@[simp] theorem bound_zsmul (c : ℤ) (I : Ineq V) : (c • I).bound = c • I.bound := rfl

instance : AddCommGroup (Ineq V) :=
  Function.Injective.addCommGroup (fun I : Ineq V => (I.coeff, I.bound))
    (fun _ _ h => Ineq.ext (congrArg Prod.fst h) (congrArg Prod.snd h)) rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The coefficients as an additive homomorphism. -/
private def coeffHom : Ineq V →+ (V →₀ ℤ) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The bound as an additive homomorphism. -/
private def boundHom : Ineq V →+ ℤ where
  toFun := bound
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Ineq V) :
    (∑ i ∈ s, f i).coeff = ∑ i ∈ s, (f i).coeff :=
  map_sum (coeffHom (V := V)) f s

@[simp] theorem bound_sum {ι : Type*} (s : Finset ι) (f : ι → Ineq V) :
    (∑ i ∈ s, f i).bound = ∑ i ∈ s, (f i).bound :=
  map_sum (boundHom (V := V)) f s

/-! ### Semantics -/

/-- The value `∑ᵥ aᵥ σ(v)` of the left-hand side of `I` under a 0/1 assignment `σ`. -/
def lhs (σ : V → Bool) (I : Ineq V) : ℤ :=
  Finsupp.linearCombination ℤ (fun v => (σ v).toInt) I.coeff

/-- The 0/1 assignment `σ` **satisfies** `I`: `∑ᵥ aᵥ σ(v) ≥ b`. -/
@[expose] def Holds (σ : V → Bool) (I : Ineq V) : Prop := I.bound ≤ I.lhs σ

@[simp] theorem lhs_zero (σ : V → Bool) : (0 : Ineq V).lhs σ = 0 := map_zero _

@[simp] theorem lhs_add (σ : V → Bool) (I J : Ineq V) : (I + J).lhs σ = I.lhs σ + J.lhs σ :=
  map_add _ _ _

@[simp] theorem lhs_nsmul (σ : V → Bool) (c : ℕ) (I : Ineq V) : (c • I).lhs σ = c * I.lhs σ := by
  simp only [lhs, coeff_nsmul, map_nsmul, nsmul_eq_mul]

/-- Scaling the coefficients by `c` scales the left-hand side. -/
theorem lhs_of_coeff_eq_smul (σ : V → Bool) {I J : Ineq V} {c : ℤ} (h : I.coeff = c • J.coeff) :
    I.lhs σ = c * J.lhs σ := by
  simp only [lhs, h, map_zsmul, smul_eq_mul]

@[simp] theorem lhs_sum (σ : V → Bool) {ι : Type*} (s : Finset ι) (f : ι → Ineq V) :
    (∑ i ∈ s, f i).lhs σ = ∑ i ∈ s, (f i).lhs σ :=
  map_sum (⟨⟨fun I => I.lhs σ, lhs_zero σ⟩, lhs_add σ⟩ : Ineq V →+ ℤ) f s

/-- The left-hand side of an inequality with a single nonzero coefficient. -/
@[simp] theorem lhs_mk_single (σ : V → Bool) (v : V) (a b : ℤ) :
    (⟨Finsupp.single v a, b⟩ : Ineq V).lhs σ = a * (σ v).toInt := by
  simp [lhs]

theorem Holds.add {σ : V → Bool} {I J : Ineq V} (hI : I.Holds σ) (hJ : J.Holds σ) :
    (I + J).Holds σ := by
  unfold Holds at *
  rw [bound_add, lhs_add]
  exact add_le_add hI hJ

theorem Holds.nsmul {σ : V → Bool} {I : Ineq V} (c : ℕ) (h : I.Holds σ) : (c • I).Holds σ := by
  unfold Holds at *
  rw [bound_nsmul, lhs_nsmul, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left h (Int.natCast_nonneg c)

/-! ### The axioms and the contradiction -/

/-- The contradiction `0 ≥ 1`. -/
@[expose] def contra : Ineq V := ⟨0, 1⟩

/-- The axiom `xᵥ ≥ 0`. -/
@[expose] def nonneg (v : V) : Ineq V := ⟨Finsupp.single v 1, 0⟩

/-- The axiom `-xᵥ ≥ -1`, that is `xᵥ ≤ 1`. -/
@[expose] def leOne (v : V) : Ineq V := ⟨Finsupp.single v (-1), -1⟩

@[simp] theorem coeff_contra : (contra : Ineq V).coeff = 0 := rfl
@[simp] theorem bound_contra : (contra : Ineq V).bound = 1 := rfl
@[simp] theorem coeff_nonneg (v : V) : (nonneg v).coeff = Finsupp.single v 1 := rfl
@[simp] theorem bound_nonneg (v : V) : (nonneg v).bound = 0 := rfl
@[simp] theorem coeff_leOne (v : V) : (leOne v).coeff = Finsupp.single v (-1) := rfl
@[simp] theorem bound_leOne (v : V) : (leOne v).bound = -1 := rfl

/-- No assignment satisfies `0 ≥ 1`. -/
theorem not_holds_contra (σ : V → Bool) : ¬ (contra : Ineq V).Holds σ := by
  simp [Holds, lhs]

theorem holds_nonneg (σ : V → Bool) (v : V) : (nonneg v).Holds σ := by
  cases h : σ v <;> simp [Holds, lhs, h]

theorem holds_leOne (σ : V → Bool) (v : V) : (leOne v).Holds σ := by
  cases h : σ v <;> simp [Holds, lhs, h]

/-- `xᵥ ≥ 0` plus `-xᵥ ≥ -1` is `0 ≥ -1`. -/
theorem nonneg_add_leOne (v : V) : nonneg v + leOne v = -contra := by
  ext <;> simp

/-! ### Rounded division -/

/-- **Rounded division** by `c` [Chvátal][Chvatal1973]: `∑ᵥ (aᵥ / c) xᵥ ≥ ⌈b / c⌉`, where `aᵥ / c`
is integer division. It is sound when `c > 0` divides every coefficient
(`Cslib.Logic.PL.Ineq.Holds.div`), the only case cutting planes use. -/
@[expose] def div (I : Ineq V) (c : ℕ) : Ineq V :=
  ⟨I.coeff.mapRange (· / (c : ℤ)) (Int.zero_ediv _), -(-I.bound / c)⟩

@[simp] theorem coeff_div (I : Ineq V) (c : ℕ) (v : V) : (I.div c).coeff v = I.coeff v / c := rfl
@[simp] theorem bound_div (I : Ineq V) (c : ℕ) : (I.div c).bound = -(-I.bound / c) := rfl

/-- `⌈b / c⌉ ≤ y` iff `b ≤ c y`. -/
theorem bound_div_le_iff {I : Ineq V} {c : ℕ} (hc : 0 < c) {y : ℤ} :
    (I.div c).bound ≤ y ↔ I.bound ≤ c * y := by
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  rw [bound_div, neg_le, Int.le_ediv_iff_mul_le hc']
  constructor <;> intro h <;> linarith

/-- If `c` divides every coefficient of `I`, multiplying the coefficients of `I.div c` by `c` gives
back those of `I`. -/
theorem smul_coeff_div {I : Ineq V} {c : ℕ} (hdvd : ∀ v, (c : ℤ) ∣ I.coeff v) :
    (c : ℤ) • (I.div c).coeff = I.coeff := by
  ext v
  simp only [Finsupp.smul_apply, coeff_div, smul_eq_mul]
  exact Int.mul_ediv_cancel' (hdvd v)

/-- **Soundness of rounded division**: if `c > 0` divides every coefficient of `I`, every 0/1
assignment satisfying `I` satisfies `I.div c`. -/
theorem Holds.div {σ : V → Bool} {I : Ineq V} {c : ℕ} (hc : 0 < c)
    (hdvd : ∀ v, (c : ℤ) ∣ I.coeff v) (h : I.Holds σ) : (I.div c).Holds σ := by
  unfold Holds at h ⊢
  rw [bound_div_le_iff hc, ← lhs_of_coeff_eq_smul σ (smul_coeff_div hdvd).symm]
  exact h

/-- Recognizing a rounded division: `I.div c = J` when the coefficients of `I` are `c` times those
of `J` and `⌈b_I / c⌉ = b_J`. -/
theorem div_eq_of {I J : Ineq V} {c : ℕ} (hc : 0 < c) (hcoeff : I.coeff = (c : ℤ) • J.coeff)
    (hlo : c * (J.bound - 1) < I.bound) (hhi : I.bound ≤ c * J.bound) : I.div c = J := by
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  ext v
  · rw [coeff_div, hcoeff, Finsupp.smul_apply, smul_eq_mul, Int.mul_ediv_cancel_left _ hc'.ne']
  · refine le_antisymm ((bound_div_le_iff hc).2 hhi) ?_
    rw [bound_div, le_neg, Int.ediv_le_iff_le_mul hc']
    linarith

end Ineq

/-! ### Clauses as inequalities -/

open Ineq

variable {V : Type*}

/-- The inequality of a literal: `xᵥ ≥ 0` for `v`, and `-xᵥ ≥ -1` (that is `1 - xᵥ ≥ 0`) for
`¬v`. -/
@[expose] def Literal.toIneq (l : Literal V) : Ineq V := bif l.2 then nonneg l.1 else leOne l.1

@[simp] theorem Literal.toIneq_true (v : V) : Literal.toIneq (v, true) = nonneg v := rfl
@[simp] theorem Literal.toIneq_false (v : V) : Literal.toIneq (v, false) = leOne v := rfl

/-- The inequality `∑_{v ∈ C} xᵥ + ∑_{¬v ∈ C} (1 - xᵥ) ≥ 1` of a clause `C`, over its distinct
literals [Jukna, Section 19.2][Jukna2012]. It is `0 ≥ 1` plus the inequalities of the distinct
literals of `C`. -/
@[expose] def Clause.toIneq [DecidableEq V] (c : Clause V) : Ineq V :=
  contra + ∑ l ∈ c.toFinset, l.toIneq

/-- `lhs - bound`, the slack. -/
private def slack (σ : V → Bool) (I : Ineq V) : ℤ := I.lhs σ - I.bound

private theorem slack_add (σ : V → Bool) (I J : Ineq V) :
    slack σ (I + J) = slack σ I + slack σ J := by
  simp only [slack, lhs_add, bound_add]; ring

private theorem slack_sum (σ : V → Bool) {ι : Type*} (s : Finset ι) (f : ι → Ineq V) :
    slack σ (∑ i ∈ s, f i) = ∑ i ∈ s, slack σ (f i) := by
  simp only [slack, lhs_sum, bound_sum, sum_sub_distrib]

private theorem slack_toIneq (σ : V → Bool) (l : Literal V) :
    slack σ l.toIneq = (Literal.eval σ l).toInt := by
  obtain ⟨v, b⟩ := l
  cases b <;> cases h : σ v <;> simp [slack, lhs, h]

/-- **The translation of clauses is faithful**: `σ` satisfies the inequality of `c` iff it
satisfies `c`. -/
theorem Clause.holds_toIneq_iff [DecidableEq V] (σ : V → Bool) (c : Clause V) :
    c.toIneq.Holds σ ↔ c.eval σ = true := by
  have hs : slack σ c.toIneq = -1 + ∑ l ∈ c.toFinset, (Literal.eval σ l).toInt := by
    simp only [toIneq, slack_add, slack_sum, slack_toIneq]
    simp [slack, lhs]
  have hnn : ∀ l ∈ c.toFinset, (0 : ℤ) ≤ (Literal.eval σ l).toInt := fun l _ => by
    cases Literal.eval σ l <;> simp
  have hpos := sum_pos_iff_of_nonneg hnn
  rw [Holds, ← sub_nonneg, ← slack, hs, Clause.eval_eq_true_iff]
  constructor
  · intro h
    obtain ⟨l, hl, hl'⟩ := hpos.1 (by linarith)
    refine ⟨l, List.mem_toFinset.1 hl, ?_⟩
    rw [← Literal.eval_eq_true_iff]
    cases h' : Literal.eval σ l <;> simp_all
  · rintro ⟨l, hl, hl'⟩
    have : 0 < ∑ l ∈ c.toFinset, (Literal.eval σ l).toInt :=
      hpos.2 ⟨l, List.mem_toFinset.2 hl, by simp [(Literal.eval_eq_true_iff σ l).2 hl']⟩
    linarith

/-- The empty clause translates to `0 ≥ 1`. -/
@[simp] theorem Clause.toIneq_nil [DecidableEq V] : Clause.toIneq ([] : Clause V) = contra := by
  simp [toIneq]

/-- For a clause without repeated literals, the translation is `0 ≥ 1` plus the list sum. -/
theorem Clause.toIneq_of_nodup [DecidableEq V] {c : Clause V} (h : c.Nodup) :
    c.toIneq = contra + (c.map Literal.toIneq).sum := by
  rw [toIneq, List.sum_toFinset _ h]

/-- The inequalities of the clauses of `φ`. -/
@[expose] def CNF.toIneqs [DecidableEq V] (φ : CNF V) : Set (Ineq V) :=
  {I | ∃ c ∈ φ, c.toIneq = I}

theorem CNF.toIneq_mem_toIneqs [DecidableEq V] {φ : CNF V} {c : Clause V} (hc : c ∈ φ) :
    c.toIneq ∈ φ.toIneqs :=
  ⟨c, hc, rfl⟩

/-- `σ` satisfies the inequalities of `φ` iff it satisfies `φ`. -/
theorem CNF.holds_toIneqs_iff [DecidableEq V] (σ : V → Bool) (φ : CNF V) :
    (∀ I ∈ φ.toIneqs, I.Holds σ) ↔ φ.eval σ = true := by
  rw [CNF.eval_eq_true_iff]
  constructor
  · intro h c hc
    exact (Clause.holds_toIneq_iff σ c).1 (h _ (toIneq_mem_toIneqs hc))
  · rintro h _ ⟨c, hc, rfl⟩
    exact (Clause.holds_toIneq_iff σ c).2 (h c hc)

/-! ### Proofs -/

namespace CuttingPlanes

/-- A **cutting planes proof** from the inequalities `Γ` [Cook, Coullard and
Turán][CookCoullardTuran1987], listed from its last line to its first: every line is in `Γ`, an
axiom `xᵥ ≥ 0` or `-xᵥ ≥ -1`, the sum of two earlier lines, an earlier line multiplied by a positive
integer, or an earlier line divided with rounding by a positive integer dividing all its
coefficients. -/
inductive IsProof (Γ : Set (Ineq V)) : List (Ineq V) → Prop
  /-- The empty proof. -/
  | nil : IsProof Γ []
  /-- An inequality of `Γ`. -/
  | hyp {ls : List (Ineq V)} {I : Ineq V} (h : IsProof Γ ls) (hI : I ∈ Γ) : IsProof Γ (I :: ls)
  /-- The axiom `xᵥ ≥ 0`. -/
  | nonneg {ls : List (Ineq V)} (h : IsProof Γ ls) (v : V) : IsProof Γ (Ineq.nonneg v :: ls)
  /-- The axiom `-xᵥ ≥ -1`. -/
  | leOne {ls : List (Ineq V)} (h : IsProof Γ ls) (v : V) : IsProof Γ (Ineq.leOne v :: ls)
  /-- The sum of two earlier lines. -/
  | add {ls : List (Ineq V)} {I J : Ineq V} (h : IsProof Γ ls) (hI : I ∈ ls) (hJ : J ∈ ls) :
      IsProof Γ ((I + J) :: ls)
  /-- An earlier line multiplied by a positive integer. -/
  | smul {ls : List (Ineq V)} {I : Ineq V} (h : IsProof Γ ls) (c : ℕ) (hc : 0 < c) (hI : I ∈ ls) :
      IsProof Γ ((c • I) :: ls)
  /-- An earlier line divided, with rounding, by a positive integer dividing its coefficients. -/
  | div {ls : List (Ineq V)} {I : Ineq V} (h : IsProof Γ ls) (c : ℕ) (hc : 0 < c)
      (hdvd : ∀ v, (c : ℤ) ∣ I.coeff v) (hI : I ∈ ls) : IsProof Γ (I.div c :: ls)

/-- `I` has a cutting planes derivation from `Γ` with at most `s` lines. -/
@[expose] def DerivableInSize (Γ : Set (Ineq V)) (I : Ineq V) (s : ℕ) : Prop :=
  ∃ ls, IsProof Γ ls ∧ I ∈ ls ∧ ls.length ≤ s

/-- `Γ` has a cutting planes refutation, a derivation of `0 ≥ 1`, with at most `s` lines. -/
@[expose] def RefutableInSize (Γ : Set (Ineq V)) (s : ℕ) : Prop := DerivableInSize Γ contra s

variable {Γ Δ : Set (Ineq V)} {ls ls' : List (Ineq V)} {I J : Ineq V} {s t : ℕ}

namespace IsProof

/-- Two proofs from `Γ` concatenate to a proof from `Γ`. -/
theorem append (h : IsProof Γ ls) (h' : IsProof Γ ls') : IsProof Γ (ls ++ ls') := by
  induction h with
  | nil => exact h'
  | hyp _ hI ih => exact ih.hyp hI
  | nonneg _ v ih => exact ih.nonneg v
  | leOne _ v ih => exact ih.leOne v
  | add _ hI hJ ih => exact ih.add (List.mem_append_left _ hI) (List.mem_append_left _ hJ)
  | smul _ c hc hI ih => exact ih.smul c hc (List.mem_append_left _ hI)
  | div _ c hc hdvd hI ih => exact ih.div c hc hdvd (List.mem_append_left _ hI)

/-- **Soundness**: every line of a proof from `Γ` holds under every 0/1 assignment satisfying
`Γ`. -/
theorem holds (h : IsProof Γ ls) {σ : V → Bool} (hσ : ∀ I ∈ Γ, I.Holds σ) (hI : I ∈ ls) :
    I.Holds σ := by
  induction h generalizing I with
  | nil => simp at hI
  | hyp _ hJ ih =>
    rcases List.mem_cons.1 hI with rfl | hI
    exacts [hσ _ hJ, ih hI]
  | nonneg _ v ih =>
    rcases List.mem_cons.1 hI with rfl | hI
    exacts [holds_nonneg σ v, ih hI]
  | leOne _ v ih =>
    rcases List.mem_cons.1 hI with rfl | hI
    exacts [holds_leOne σ v, ih hI]
  | add _ h₁ h₂ ih =>
    rcases List.mem_cons.1 hI with rfl | hI
    exacts [(ih h₁).add (ih h₂), ih hI]
  | smul _ c _ h₁ ih =>
    rcases List.mem_cons.1 hI with rfl | hI
    exacts [(ih h₁).nsmul c, ih hI]
  | div _ c hc hdvd h₁ ih =>
    rcases List.mem_cons.1 hI with rfl | hI
    exacts [(ih h₁).div hc hdvd, ih hI]

/-- **Composing proofs**: a proof `ls'` from `Δ` replays on top of a proof `ls` from `Γ` when every
inequality of `Δ` is in `Γ` or a line of `ls`, adding at most as many lines as `ls'` has. -/
theorem comp (hΔ : IsProof Δ ls') (h : IsProof Γ ls) (hΔΓ : ∀ I ∈ Δ, I ∈ Γ ∨ I ∈ ls) :
    ∃ ls'', IsProof Γ (ls'' ++ ls) ∧ (∀ I ∈ ls', I ∈ ls'' ++ ls) ∧ ls''.length ≤ ls'.length := by
  induction hΔ with
  | nil => exact ⟨[], h, by simp, le_rfl⟩
  | @hyp ls' I _ hI ih =>
    obtain ⟨ls'', h'', hup, hlen⟩ := ih
    rcases hΔΓ I hI with hI | hI
    · refine ⟨I :: ls'', h''.hyp hI, fun J hJ => ?_, by simpa using hlen⟩
      rcases List.mem_cons.1 hJ with rfl | hJ
      exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hup J hJ)]
    · refine ⟨ls'', h'', fun J hJ => ?_, hlen.trans (Nat.le_succ _)⟩
      rcases List.mem_cons.1 hJ with rfl | hJ
      exacts [List.mem_append_right _ hI, hup J hJ]
  | @nonneg ls' _ v ih =>
    obtain ⟨ls'', h'', hup, hlen⟩ := ih
    refine ⟨_ :: ls'', h''.nonneg v, fun J hJ => ?_, by simpa using hlen⟩
    rcases List.mem_cons.1 hJ with rfl | hJ
    exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hup J hJ)]
  | @leOne ls' _ v ih =>
    obtain ⟨ls'', h'', hup, hlen⟩ := ih
    refine ⟨_ :: ls'', h''.leOne v, fun J hJ => ?_, by simpa using hlen⟩
    rcases List.mem_cons.1 hJ with rfl | hJ
    exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hup J hJ)]
  | @add ls' I₁ I₂ _ h₁ h₂ ih =>
    obtain ⟨ls'', h'', hup, hlen⟩ := ih
    refine ⟨_ :: ls'', h''.add (hup _ h₁) (hup _ h₂), fun J hJ => ?_, by simpa using hlen⟩
    rcases List.mem_cons.1 hJ with rfl | hJ
    exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hup J hJ)]
  | @smul ls' I₁ _ c hc h₁ ih =>
    obtain ⟨ls'', h'', hup, hlen⟩ := ih
    refine ⟨_ :: ls'', h''.smul c hc (hup _ h₁), fun J hJ => ?_, by simpa using hlen⟩
    rcases List.mem_cons.1 hJ with rfl | hJ
    exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hup J hJ)]
  | @div ls' I₁ _ c hc hdvd h₁ ih =>
    obtain ⟨ls'', h'', hup, hlen⟩ := ih
    refine ⟨_ :: ls'', h''.div c hc hdvd (hup _ h₁), fun J hJ => ?_, by simpa using hlen⟩
    rcases List.mem_cons.1 hJ with rfl | hJ
    exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hup J hJ)]

end IsProof

namespace DerivableInSize

/-- An inequality of `Γ` is derivable in one line. -/
theorem hyp (hI : I ∈ Γ) : DerivableInSize Γ I 1 := ⟨[I], IsProof.nil.hyp hI, by simp, le_rfl⟩

/-- The axiom `xᵥ ≥ 0` is derivable in one line. -/
theorem nonneg (v : V) : DerivableInSize Γ (Ineq.nonneg v) 1 :=
  ⟨_, IsProof.nil.nonneg v, List.mem_singleton_self _, le_rfl⟩

/-- The axiom `-xᵥ ≥ -1` is derivable in one line. -/
theorem leOne (v : V) : DerivableInSize Γ (Ineq.leOne v) 1 :=
  ⟨_, IsProof.nil.leOne v, List.mem_singleton_self _, le_rfl⟩

/-- The inequality of a literal is an axiom, derivable in one line. -/
theorem literal (l : Literal V) : DerivableInSize Γ l.toIneq 1 := by
  obtain ⟨v, b⟩ := l
  cases b
  exacts [leOne v, nonneg v]

theorem mono (h : DerivableInSize Γ I s) (hst : s ≤ t) : DerivableInSize Γ I t :=
  let ⟨ls, h, hI, hlen⟩ := h
  ⟨ls, h, hI, hlen.trans hst⟩

theorem add (hI : DerivableInSize Γ I s) (hJ : DerivableInSize Γ J t) :
    DerivableInSize Γ (I + J) (s + t + 1) := by
  obtain ⟨ls, h, hI, hlen⟩ := hI
  obtain ⟨ls', h', hJ, hlen'⟩ := hJ
  refine ⟨_, (h.append h').add (List.mem_append_left _ hI) (List.mem_append_right _ hJ),
    List.mem_cons_self, ?_⟩
  simp only [List.length_cons, List.length_append]
  omega

theorem smul (hI : DerivableInSize Γ I s) (c : ℕ) (hc : 0 < c) :
    DerivableInSize Γ (c • I) (s + 1) :=
  let ⟨_, h, hI, hlen⟩ := hI
  ⟨_, h.smul c hc hI, List.mem_cons_self, by simpa using hlen⟩

theorem div (hI : DerivableInSize Γ I s) (c : ℕ) (hc : 0 < c)
    (hdvd : ∀ v, (c : ℤ) ∣ I.coeff v) : DerivableInSize Γ (I.div c) (s + 1) :=
  let ⟨_, h, hI, hlen⟩ := hI
  ⟨_, h.div c hc hdvd hI, List.mem_cons_self, by simpa using hlen⟩

/-- Adding a family of derivable inequalities to a derivable inequality, one at a time. -/
theorem add_sum {ι : Type*} {f : ι → Ineq V} {r : ℕ} (u : Finset ι)
    (hI : DerivableInSize Γ I s) (hf : ∀ i ∈ u, DerivableInSize Γ (f i) r) :
    DerivableInSize Γ (I + ∑ i ∈ u, f i) (s + #u * (r + 1)) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using hI
  | @insert a u ha ih =>
    have := (ih fun i hi => hf i (mem_insert_of_mem hi)).add (hf a (mem_insert_self a u))
    rw [sum_insert ha, card_insert_of_notMem ha, ← add_assoc, add_right_comm I]
    exact this.mono (by rw [Nat.succ_mul]; omega)

/-- The sum of a nonempty family of derivable inequalities. -/
theorem sum {ι : Type*} {f : ι → Ineq V} {r : ℕ} {u : Finset ι} (hu : u.Nonempty)
    (hf : ∀ i ∈ u, DerivableInSize Γ (f i) r) :
    DerivableInSize Γ (∑ i ∈ u, f i) (#u * (r + 1)) := by
  induction hu using Finset.Nonempty.cons_induction with
  | singleton a => simpa using (hf a (mem_singleton_self a)).mono (Nat.le_succ r)
  | cons a u ha hu ih =>
    have := (hf a (mem_cons_self a u)).add (ih fun i hi => hf i (mem_cons.2 (Or.inr hi)))
    rw [sum_cons, card_cons]
    exact this.mono (by rw [Nat.succ_mul]; omega)

/-- **Soundness** of derivations. -/
theorem holds (h : DerivableInSize Γ I s) {σ : V → Bool} (hσ : ∀ J ∈ Γ, J.Holds σ) : I.Holds σ :=
  let ⟨_, h, hI, _⟩ := h
  h.holds hσ hI

/-- Replay a derivation from `Δ` on top of a proof `ls` from `Γ` when every inequality of `Δ` is in
`Γ` or a line of `ls`. -/
theorem extend (hD : DerivableInSize Δ I t) (h : IsProof Γ ls)
    (hΔΓ : ∀ J ∈ Δ, J ∈ Γ ∨ J ∈ ls) :
    ∃ ls'', IsProof Γ (ls'' ++ ls) ∧ I ∈ ls'' ++ ls ∧ ls''.length ≤ t :=
  let ⟨_, hD, hI, hlen⟩ := hD
  let ⟨ls'', h'', hup, hlen'⟩ := hD.comp h hΔΓ
  ⟨ls'', h'', hup _ hI, hlen'.trans hlen⟩

end DerivableInSize

/-- **Soundness of cutting planes**: a refutable system has no 0/1 solution. -/
theorem RefutableInSize.not_exists_holds (h : RefutableInSize Γ s) :
    ¬ ∃ σ : V → Bool, ∀ I ∈ Γ, I.Holds σ :=
  fun ⟨σ, hσ⟩ => not_holds_contra σ (DerivableInSize.holds h hσ)

theorem RefutableInSize.mono (h : RefutableInSize Γ s) (hst : s ≤ t) : RefutableInSize Γ t :=
  DerivableInSize.mono h hst

/-- **Soundness of cutting planes for CNFs**: a CNF whose inequalities are refutable is
unsatisfiable. -/
theorem RefutableInSize.not_satisfiable [DecidableEq V] {φ : CNF V}
    (h : RefutableInSize φ.toIneqs s) : ¬ φ.Satisfiable :=
  fun ⟨σ, hσ⟩ => h.not_exists_holds ⟨σ, (CNF.holds_toIneqs_iff σ φ).2 hσ⟩

end CuttingPlanes

end

end Cslib.Logic.PL
