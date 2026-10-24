/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Fourier
public import Complexity.Logics.Propositional.CNF
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fintype.Fin

/-!
# Unsatisfiability value of CNF formulas and the `7 / 8` random-assignment bound

The **unsatisfiability value** `CNF.unsatVal φ` of a formula in conjunctive normal form is the
least proportion of its clauses, counted with multiplicity, that an assignment falsifies
(`CNF.countUnsat`). The value vanishes on the empty formula and on satisfiable formulas
(`CNF.unsatVal_eq_zero_iff`), and `1 - CNF.unsatVal φ` is the value of `φ` as an instance of
MAX-SAT.

When the three variables of every clause are distinct (`CNF.IsExactThreeDistinct`), a uniform
random assignment falsifies each clause with probability `1 / 8`
(`Clause.IsExactThreeDistinct.expect_eval_eq_false`), so some assignment falsifies at most `1 / 8`
of the clauses (`CNF.IsExactThreeDistinct.unsatVal_le_one_eighth`). Håstad showed that this
`7 / 8` threshold is optimal [Hastad2001].

## Main definitions

* `Cslib.Logic.PL.CNF.unsatVal`: the least proportion of falsified clauses.
* `Cslib.Logic.PL.Clause.IsExactThreeDistinct`, `Cslib.Logic.PL.CNF.IsExactThreeDistinct`: clauses
  and formulas with three distinct variables per clause.

## Main results

* `Cslib.Logic.PL.CNF.countUnsat_eq_card`: the number of falsified clauses as a cardinality over
  clause indices.
* `Cslib.Logic.PL.CNF.unsatVal_eq_zero_iff`: the value vanishes exactly on satisfiable formulas.
* `Cslib.Logic.PL.CNF.length_pos_of_unsatVal_pos`: a formula of positive value has a clause.
* `Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_false`,
  `Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_true`: a uniform random assignment
  falsifies a clause with three distinct variables with probability `1 / 8`.
* `Cslib.Logic.PL.CNF.IsExactThreeDistinct.unsatVal_le_one_eighth`,
  `Cslib.Logic.PL.CNF.IsExactThreeDistinct.exists_countUnsat_le_div_eight`: the `7 / 8`
  random-assignment bound.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
-/

@[expose] public section

open Finset Cslib.BitString
open scoped BigOperators

namespace Cslib.Logic.PL

variable {V W ι : Type*}

/-! ### Counting falsified clauses -/

/-- The number of falsified clauses, counted by their positions in the formula. -/
theorem CNF.countUnsat_eq_card (σ : V → Bool) (φ : CNF V) :
    φ.countUnsat σ = #{j : Fin φ.length | φ[j].eval σ = false} := by
  have key (p : Clause V → Bool) (l : CNF V) :
      l.countP p = #{j : Fin l.length | p l[j] = true} := by
    induction l with
    | nil => simp
    | cons a l ih =>
      change _ = #{j : Fin (l.length + 1) | p (a :: l)[j] = true}
      rw [List.countP_cons, ih, Fin.card_filter_univ_succ', add_comm]
      simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
        List.getElem_cons_succ]
      congr
  simp [countUnsat, key]

/-- Relabelling counts the falsified clauses of the composite assignment. -/
theorem CNF.countUnsat_relabel (φ : CNF V) (f : V → W) (τ : W → Bool) :
    (φ.relabel f).countUnsat τ = φ.countUnsat (τ ∘ f) := by
  simp only [CNF.countUnsat, CNF.relabel, List.countP_map]
  exact List.countP_congr fun c _ => by simp [Function.comp_def]

/-! ### The value of a formula -/

/-- The **unsatisfiability value** of a formula: the least proportion of its clauses, counted with
multiplicity, that an assignment falsifies. The formula without clauses has value zero. -/
noncomputable def CNF.unsatVal (φ : CNF V) : ℝ :=
  ⨅ σ : V → Bool, (φ.countUnsat σ : ℝ) / φ.length

namespace CNF

variable (φ : CNF V)

/-- The proportions of falsified clauses are bounded below, by zero. -/
private theorem bddBelow_range_countUnsat_div :
    BddBelow (Set.range fun σ : V → Bool => (φ.countUnsat σ : ℝ) / φ.length) :=
  ⟨0, Set.forall_mem_range.2 fun _ => by positivity⟩

/-- The value is at most the proportion of the clauses that any assignment falsifies. -/
theorem unsatVal_le (σ : V → Bool) : φ.unsatVal ≤ φ.countUnsat σ / φ.length :=
  ciInf_le (bddBelow_range_countUnsat_div φ) σ

/-- The value is nonnegative. -/
theorem unsatVal_nonneg : 0 ≤ φ.unsatVal :=
  Real.iInf_nonneg fun _ => by positivity

/-- A lower bound on the value bounds the proportion falsified by every assignment. -/
theorem le_unsatVal_iff {c : ℝ} : c ≤ φ.unsatVal ↔ ∀ σ : V → Bool, c ≤ φ.countUnsat σ / φ.length :=
  le_ciInf_iff (bddBelow_range_countUnsat_div φ)

/-- The minimum is attained: the proportions take finitely many values. -/
theorem exists_countUnsat_div_eq_unsatVal :
    ∃ σ : V → Bool, (φ.countUnsat σ : ℝ) / φ.length = φ.unsatVal := by
  have hfin : (Set.range fun σ : V → Bool => (φ.countUnsat σ : ℝ) / φ.length).Finite := by
    refine (Set.finite_range fun j : Fin (φ.length + 1) => (j : ℝ) / φ.length).subset ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨⟨_, Nat.lt_succ_of_le (φ.countUnsat_le_length σ)⟩, rfl⟩
  exact (Set.range_nonempty _).csInf_mem hfin

/-- **The value vanishes exactly on satisfiable formulas.** -/
theorem unsatVal_eq_zero_iff : φ.unsatVal = 0 ↔ φ.Satisfiable := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := φ.exists_countUnsat_div_eq_unsatVal
    rw [h, div_eq_zero_iff, Nat.cast_eq_zero, Nat.cast_eq_zero] at hσ
    rcases hσ with hσ | hσ
    · exact ⟨σ, countUnsat_eq_zero_iff.1 hσ⟩
    · exact ⟨σ, by rw [List.length_eq_zero_iff.1 hσ]; rfl⟩
  · rintro ⟨σ, hσ⟩
    refine le_antisymm ?_ φ.unsatVal_nonneg
    simpa [countUnsat_eq_zero_iff.2 hσ] using φ.unsatVal_le σ

/-- A formula in which every assignment falsifies a positive proportion of the clauses has a
clause. -/
theorem length_pos_of_unsatVal_pos {φ : CNF V} (h : 0 < φ.unsatVal) : 0 < φ.length := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have hsat : φ.Satisfiable := ⟨fun _ => false, by rw [List.length_eq_zero_iff.1 h0]; rfl⟩
  rw [(unsatVal_eq_zero_iff φ).2 hsat] at h
  exact lt_irrefl _ h

end CNF

/-! ### Exact 3-clauses with distinct variables and the `7 / 8` random assignment bound -/

/-- A clause has **three distinct variables** when it has length `3` and its variables have no
duplicates. -/
def Clause.IsExactThreeDistinct (c : Clause V) : Prop :=
  c.length = 3 ∧ (c.map Prod.fst).Nodup

/-- A formula is an **exact 3-CNF with distinct variables per clause** when every clause has three
distinct variables. -/
def CNF.IsExactThreeDistinct (φ : CNF V) : Prop :=
  ∀ c ∈ φ, c.IsExactThreeDistinct

/-- Whether a clause has three distinct variables is decidable. -/
instance [DecidableEq V] {c : Clause V} : Decidable c.IsExactThreeDistinct :=
  inferInstanceAs (Decidable (c.length = 3 ∧ (c.map Prod.fst).Nodup))

/-- Whether every clause of a CNF formula has three distinct variables is decidable. -/
instance [DecidableEq V] {φ : CNF V} : Decidable φ.IsExactThreeDistinct :=
  inferInstanceAs (Decidable (∀ c ∈ φ, c.IsExactThreeDistinct))

/-- An exact 3-clause with distinct variables has length `3`. -/
theorem Clause.IsExactThreeDistinct.length_eq {c : Clause V} (hc : c.IsExactThreeDistinct) :
    c.length = 3 :=
  hc.1

/-- The variables of an exact 3-clause with distinct variables have no duplicates. -/
theorem Clause.IsExactThreeDistinct.nodup_map_fst {c : Clause V} (hc : c.IsExactThreeDistinct) :
    (c.map Prod.fst).Nodup :=
  hc.2

/-- Every exact 3-clause with distinct variables is a list of three literals on pairwise distinct
variables. -/
theorem Clause.isExactThreeDistinct_iff {c : Clause V} :
    c.IsExactThreeDistinct ↔
      ∃ l₁ l₂ l₃ : Literal V,
        c = [l₁, l₂, l₃] ∧ l₁.1 ≠ l₂.1 ∧ l₁.1 ≠ l₃.1 ∧ l₂.1 ≠ l₃.1 := by
  constructor
  · rintro ⟨hlen, hnodup⟩
    match c, hlen with
    | [l₁, l₂, l₃], _ =>
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or, List.nodup_nil, and_true] at hnodup
      exact ⟨l₁, l₂, l₃, rfl, hnodup.1.1, hnodup.1.2, hnodup.2.1⟩
  · rintro ⟨l₁, l₂, l₃, rfl, h12, h13, h23⟩
    refine ⟨rfl, ?_⟩
    simp [h12, h13, h23]

/-- The falsification indicator of a literal `(v, b)` under `σ` is
`(1 - signVal b * signVal (σ v)) / 2`. -/
private theorem Literal.if_eval_eq_zero_one (l : Literal V) (σ : V → Bool) :
    (if l.eval σ then (0 : ℝ) else 1) = (1 - signVal l.2 * signVal (σ l.1)) / 2 := by
  rcases l with ⟨v, b⟩
  cases b <;> cases h : σ v <;> simp [Literal.eval, signVal, h]

/-- A clause `l :: c` is falsified iff both `l` and `c` are falsified. -/
private theorem Clause.if_eval_cons_eq_mul (l : Literal V) (c : Clause V) (σ : V → Bool) :
    (if Clause.eval σ (l :: c) then (0 : ℝ) else 1) =
      (if l.eval σ then (0 : ℝ) else 1) * (if c.eval σ then (0 : ℝ) else 1) := by
  rw [Clause.eval_cons]
  cases l.eval σ <;> cases c.eval σ <;> simp

section FintypeCube

variable [Fintype ι] [DecidableEq ι]

/-- Over a uniform random assignment `σ : ι → Bool`, a single variable has mean sign `0`. -/
private theorem expect_signVal_eval (v : ι) : (𝔼 σ : ι → Bool, signVal (σ v)) = 0 := by
  have h : (fun σ : ι → Bool => signVal (σ v)) = chi ℝ {v} := by
    funext σ
    exact (chi_singleton v σ).symm
  rw [h, expect_chi, ite_eq_right_iff.2 fun h0 => absurd h0 (singleton_ne_empty v)]

/-- Over a uniform random assignment `σ : ι → Bool`, two distinct variables have uncorrelated
signs. -/
private theorem expect_signVal_mul_of_ne {v₁ v₂ : ι} (h12 : v₁ ≠ v₂) :
    (𝔼 σ : ι → Bool, signVal (σ v₁) * signVal (σ v₂)) = 0 := by
  have h : (fun σ : ι → Bool => signVal (σ v₁) * signVal (σ v₂)) =
      fun σ => chi ℝ {v₁} σ * chi ℝ {v₂} σ := by
    funext σ
    rw [chi_singleton, chi_singleton]
  rw [h, expect_chi_mul_chi, ite_eq_right_iff.2 fun h0 => absurd h0 (singleton_injective.ne h12)]

/-- Over a uniform random assignment `σ : ι → Bool`, three pairwise distinct variables have zero
triple sign correlation. -/
private theorem expect_signVal_mul_three_of_ne {v₁ v₂ v₃ : ι} (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃)
    (h23 : v₂ ≠ v₃) :
    (𝔼 σ : ι → Bool, signVal (σ v₁) * signVal (σ v₂) * signVal (σ v₃)) = 0 := by
  have h : (fun σ : ι → Bool => signVal (σ v₁) * signVal (σ v₂) * signVal (σ v₃)) =
      chi ℝ ({v₁, v₂, v₃} : Finset ι) := by
    funext σ
    have hnot1 : v₁ ∉ ({v₂, v₃} : Finset ι) := by simp [h12, h13]
    have hnot2 : v₂ ∉ ({v₃} : Finset ι) := by simp [h23]
    rw [chi_eq_prod_signVal, prod_insert hnot1, prod_insert hnot2, prod_singleton, mul_assoc]
  rw [h, expect_chi, ite_eq_right_iff.2 fun h0 => absurd h0 (insert_ne_empty _ _)]

/-- **A uniform random assignment falsifies any 3-clause on three distinct variables with
probability `1 / 8`.** -/
theorem Clause.IsExactThreeDistinct.expect_eval_eq_false {c : Clause ι}
    (hc : c.IsExactThreeDistinct) :
    (𝔼 σ : ι → Bool, if c.eval σ then (0 : ℝ) else 1) = 1 / 8 := by
  obtain ⟨l₁, l₂, l₃, rfl, h12, h13, h23⟩ := Clause.isExactThreeDistinct_iff.1 hc
  have hexp (σ : ι → Bool) :
      (if Clause.eval σ [l₁, l₂, l₃] then (0 : ℝ) else 1) =
        1 / 8 -
        (signVal l₁.2 / 8) * signVal (σ l₁.1) -
        (signVal l₂.2 / 8) * signVal (σ l₂.1) -
        (signVal l₃.2 / 8) * signVal (σ l₃.1) +
        (signVal l₁.2 * signVal l₂.2 / 8) * (signVal (σ l₁.1) * signVal (σ l₂.1)) +
        (signVal l₁.2 * signVal l₃.2 / 8) * (signVal (σ l₁.1) * signVal (σ l₃.1)) +
        (signVal l₂.2 * signVal l₃.2 / 8) * (signVal (σ l₂.1) * signVal (σ l₃.1)) -
        (signVal l₁.2 * signVal l₂.2 * signVal l₃.2 / 8) *
          (signVal (σ l₁.1) * signVal (σ l₂.1) * signVal (σ l₃.1)) := by
    rw [Clause.if_eval_cons_eq_mul, Clause.if_eval_cons_eq_mul, Clause.if_eval_cons_eq_mul]
    simp only [Clause.eval_nil, Bool.false_eq_true, ↓reduceIte, mul_one,
      Literal.if_eval_eq_zero_one]
    ring
  simp only [hexp, expect_sub_distrib, expect_add_distrib, Fintype.expect_const, ← mul_expect,
    expect_signVal_eval, expect_signVal_mul_of_ne h12, expect_signVal_mul_of_ne h13,
    expect_signVal_mul_of_ne h23, expect_signVal_mul_three_of_ne h12 h13 h23]
  ring

/-- **A uniform random assignment satisfies any 3-clause on three distinct variables with
probability `7 / 8`.** -/
theorem Clause.IsExactThreeDistinct.expect_eval_eq_true {c : Clause ι}
    (hc : c.IsExactThreeDistinct) :
    (𝔼 σ : ι → Bool, if c.eval σ then (1 : ℝ) else 0) = 7 / 8 := by
  have h1 (σ : ι → Bool) :
      (if c.eval σ then (1 : ℝ) else 0) = 1 - (if c.eval σ then (0 : ℝ) else 1) := by
    cases c.eval σ <;> norm_num
  simp only [h1, expect_sub_distrib, Fintype.expect_const, hc.expect_eval_eq_false]
  ring

/-- Over the 3-bit cube `Fin 3 → Bool`, any 3-clause on three distinct variables is satisfied by
exactly `7` of the `8` truth assignments. -/
theorem Clause.IsExactThreeDistinct.card_eval_eq_true {c : Clause (Fin 3)}
    (hc : c.IsExactThreeDistinct) :
    #{σ : Fin 3 → Bool | c.eval σ = true} = 7 := by
  have h := hc.expect_eval_eq_true
  rw [Fintype.expect_eq_sum_div_card, sum_boole] at h
  have hcard : (Fintype.card (Fin 3 → Bool) : ℝ) = 8 := by norm_num
  rw [hcard] at h
  have h7 : ((#{σ : Fin 3 → Bool | c.eval σ = true} : ℕ) : ℝ) = 7 := by linarith
  exact_mod_cast h7

/-- The expected number of falsified clauses in an exact 3-CNF formula with distinct variables per
clause under a uniform random assignment is `φ.length / 8`. -/
private theorem CNF.IsExactThreeDistinct.expect_countUnsat {φ : CNF ι}
    (hφ : φ.IsExactThreeDistinct) :
    (𝔼 σ : ι → Bool, (φ.countUnsat σ : ℝ)) = (φ.length : ℝ) / 8 := by
  induction φ with
  | nil => simp [CNF.countUnsat]
  | cons c φ ih =>
    have hc : c.IsExactThreeDistinct := hφ c List.mem_cons_self
    have hφ' : CNF.IsExactThreeDistinct φ := fun d hd => hφ d (List.mem_cons_of_mem _ hd)
    have hcons (σ : ι → Bool) :
        ((CNF.countUnsat σ (c :: φ) : ℕ) : ℝ) =
          (if c.eval σ then (0 : ℝ) else 1) + (CNF.countUnsat σ φ : ℝ) := by
      rw [CNF.countUnsat, List.countP_cons, ← CNF.countUnsat]
      cases c.eval σ <;> simp [add_comm]
    simp only [hcons, expect_add_distrib, hc.expect_eval_eq_false, ih hφ', List.length_cons,
      Nat.cast_add, Nat.cast_one]
    ring

end FintypeCube

/-- Relabelling a clause along a map that is injective on its variables preserves
`Clause.IsExactThreeDistinct`. -/
private theorem Clause.IsExactThreeDistinct.relabel_of_injOn {f : V → ι} {c : Clause V}
    (hf : ∀ x ∈ c.map Prod.fst, ∀ y ∈ c.map Prod.fst, f x = f y → x = y)
    (hc : c.IsExactThreeDistinct) : (c.relabel f).IsExactThreeDistinct := by
  refine ⟨by rw [Clause.length_relabel, hc.1], ?_⟩
  have hmap : (c.relabel f).map Prod.fst = (c.map Prod.fst).map f := by
    simp [Clause.relabel, List.map_map, Function.comp_def]
  rw [hmap]
  exact hc.2.map_on hf

/-- **The `7 / 8` random-assignment bound**: in every exact 3-CNF formula `φ` with three distinct
variables per clause, some assignment falsifies at most `1 / 8` of the clauses
(`φ.unsatVal ≤ 1 / 8`), hence satisfies at least `7 / 8` of the clauses. -/
theorem CNF.IsExactThreeDistinct.unsatVal_le_one_eighth {φ : CNF V}
    (hφ : φ.IsExactThreeDistinct) : φ.unsatVal ≤ 1 / 8 := by
  classical
  let S : Finset V := φ.vars.toFinset
  let toVar (v : V) : Option S := if h : v ∈ S then some ⟨v, h⟩ else none
  have hφ' : (φ.relabel toVar).IsExactThreeDistinct := by
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    refine (hφ c hc).relabel_of_injOn fun x hx y hy hxy => ?_
    obtain ⟨lx, hlx, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ly, hly, rfl⟩ := List.mem_map.1 hy
    have hxS : lx.1 ∈ S := List.mem_toFinset.2 (CNF.mem_vars.2 ⟨c, hc, lx.2, hlx⟩)
    have hyS : ly.1 ∈ S := List.mem_toFinset.2 (CNF.mem_vars.2 ⟨c, hc, ly.2, hly⟩)
    simp only [toVar, hxS, hyS, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hxy
    exact hxy
  have hle : φ.unsatVal ≤ (φ.relabel toVar).unsatVal := by
    refine le_ciInf fun τ => ?_
    rw [CNF.countUnsat_relabel, CNF.relabel, List.length_map]
    exact φ.unsatVal_le (τ ∘ toVar)
  refine hle.trans ?_
  rcases Nat.eq_zero_or_pos (φ.relabel toVar).length with h0 | hpos
  · have hsat : (φ.relabel toVar).Satisfiable :=
      ⟨fun _ => false, by rw [List.length_eq_zero_iff.1 h0]; rfl⟩
    rw [(CNF.unsatVal_eq_zero_iff _).2 hsat]
    norm_num
  · have hlen : (0 : ℝ) < (φ.relabel toVar).length := by exact_mod_cast hpos
    have hle' : (φ.relabel toVar).unsatVal ≤
        𝔼 σ : Option S → Bool, ((φ.relabel toVar).countUnsat σ : ℝ) / (φ.relabel toVar).length := by
      simpa only [Fintype.expect_const] using
        expect_le_expect (s := univ) fun σ _ => (φ.relabel toVar).unsatVal_le σ
    rw [← expect_div, hφ'.expect_countUnsat, div_right_comm, div_self hlen.ne'] at hle'
    exact hle'

/-- In every exact 3-CNF formula `φ` with three distinct variables per clause, there exists an
assignment falsifying at most `φ.length / 8` clauses (equivalently satisfying at least
`7 / 8 * φ.length` clauses). -/
theorem CNF.IsExactThreeDistinct.exists_countUnsat_le_div_eight {φ : CNF V}
    (hφ : φ.IsExactThreeDistinct) :
    ∃ σ : V → Bool, (φ.countUnsat σ : ℝ) ≤ (φ.length : ℝ) / 8 := by
  obtain ⟨σ, hσ⟩ := φ.exists_countUnsat_div_eq_unsatVal
  refine ⟨σ, ?_⟩
  rcases Nat.eq_zero_or_pos φ.length with h0 | hpos
  · have hc0 : φ.countUnsat σ = 0 := Nat.le_zero.1 ((φ.countUnsat_le_length σ).trans_eq h0)
    simp [hc0, h0]
  · have hlen : (0 : ℝ) < φ.length := by exact_mod_cast hpos
    have hle := hφ.unsatVal_le_one_eighth
    rw [← hσ, div_le_iff₀ hlen] at hle
    linarith

end Cslib.Logic.PL
