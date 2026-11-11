/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card

/-!
# The implication graph of a formula with clauses of width two

A clause `a ∨ b` says both `¬a → b` and `¬b → a`, and a unit clause `a` says `¬a → a`. The
implication graph of a formula (`Cslib.Logic.PL.CNF.Implies`) has these arcs between literals:
an arc from `ℓ` to `ℓ'` when some clause contains `¬ℓ` and `ℓ'` and no other literal. Every arc
is an implication that holds under a satisfying assignment, so a formula with a path from some
literal `x` to `¬x` and one back is unsatisfiable (`Cslib.Logic.PL.CNF.not_satisfiable_of_reach`).
For clauses of width at most two the converse holds: a formula without the empty clause and
without such a pair of paths is satisfiable
(`Cslib.Logic.PL.CNF.not_satisfiable_iff_of_width_le_two`) [Aspvall, Plass and
Tarjan][AspvallPlassTarjan1979]. The proof picks a literal `ℓ` with no path to `¬ℓ`, makes every
literal reachable from `ℓ` true, which is consistent and satisfies every clause it touches, and
continues with the remaining clauses, which mention fewer variables. The empty clause, which has
no arcs, is excluded separately; this proof is the library's own.

## Main definitions

* `Cslib.Logic.PL.CNF.Implies`: the implication graph.

## Main results

* `Cslib.Logic.PL.CNF.Implies.negate`: the implication graph is skew-symmetric.
* `Cslib.Logic.PL.CNF.not_satisfiable_of_reach`: a path from a literal to its negation and back
  refutes a formula.
* `Cslib.Logic.PL.CNF.satisfiable_of_width_le_two`: the converse for clauses of width at most two.
* `Cslib.Logic.PL.CNF.not_satisfiable_iff_of_width_le_two`: the characterization.

## References

* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Sat (Literal)

variable {V : Type*}

/-- **The implication graph** of a formula: an arc from `ℓ` to `ℓ'` when some clause contains
`¬ℓ` and `ℓ'` and no other literal. A clause `a ∨ b` gives the arcs `¬a → b` and `¬b → a`, and a
unit clause `a` the arc `¬a → a`. -/
def CNF.Implies (φ : CNF V) (ℓ ℓ' : Literal V) : Prop :=
  ∃ c ∈ φ, ℓ.negate ∈ c ∧ ℓ' ∈ c ∧ ∀ m ∈ c, m = ℓ.negate ∨ m = ℓ'

@[simp]
theorem negate_negate (ℓ : Literal V) : ℓ.negate.negate = ℓ := by
  obtain ⟨v, b⟩ := ℓ
  simp [Std.Sat.Literal.negate]

/-- The negation of a literal holds exactly when the literal does not. -/
theorem holds_negate (σ : V → Bool) (ℓ : Literal V) :
    σ ℓ.negate.1 = ℓ.negate.2 ↔ ¬ σ ℓ.1 = ℓ.2 := by
  obtain ⟨v, b⟩ := ℓ
  cases b <;> simp [Std.Sat.Literal.negate]

namespace CNF.Implies

variable {φ ψ : CNF V} {ℓ ℓ' : Literal V}

/-- **The implication graph is skew-symmetric**: the contrapositive of an arc is an arc. -/
theorem negate (h : φ.Implies ℓ ℓ') : φ.Implies ℓ'.negate ℓ.negate := by
  obtain ⟨c, hc, h₁, h₂, h₃⟩ := h
  refine ⟨c, hc, by rwa [negate_negate], h₁, fun m hm => ?_⟩
  rw [negate_negate]
  exact (h₃ m hm).symm

/-- An arc is an implication under every satisfying assignment. -/
theorem eval {σ : V → Bool} (hσ : φ.eval σ = true) (h : φ.Implies ℓ ℓ')
    (hℓ : σ ℓ.1 = ℓ.2) : σ ℓ'.1 = ℓ'.2 := by
  obtain ⟨c, hc, -, -, h₃⟩ := h
  obtain ⟨m, hm, hmσ⟩ := (Clause.eval_eq_true_iff σ c).mp ((CNF.eval_eq_true_iff σ φ).mp hσ c hc)
  rcases h₃ m hm with rfl | rfl
  · exact absurd hℓ ((holds_negate σ ℓ).mp hmσ)
  · exact hmσ

/-- The implication graph grows with the formula. -/
theorem mono (h : φ.Implies ℓ ℓ') (hφ : ∀ c ∈ φ, c ∈ ψ) : ψ.Implies ℓ ℓ' :=
  let ⟨c, hc, h⟩ := h
  ⟨c, hφ c hc, h⟩

end CNF.Implies

/-- Paths of the implication graph are skew-symmetric too. -/
theorem CNF.reach_negate {φ : CNF V} {ℓ ℓ' : Literal V}
    (h : Relation.ReflTransGen φ.Implies ℓ ℓ') :
    Relation.ReflTransGen φ.Implies ℓ'.negate ℓ.negate := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.head hab.negate

/-- Paths of the implication graph are implications under every satisfying assignment. -/
theorem CNF.eval_of_reach {φ : CNF V} {σ : V → Bool} (hσ : φ.eval σ = true) {ℓ ℓ' : Literal V}
    (h : Relation.ReflTransGen φ.Implies ℓ ℓ') (hℓ : σ ℓ.1 = ℓ.2) : σ ℓ'.1 = ℓ'.2 := by
  induction h with
  | refl => exact hℓ
  | tail _ hab ih => exact hab.eval hσ ih

/-- **A path from a literal to its negation and back refutes a formula.** -/
theorem CNF.not_satisfiable_of_reach {φ : CNF V} {ℓ : Literal V}
    (h₁ : Relation.ReflTransGen φ.Implies ℓ ℓ.negate)
    (h₂ : Relation.ReflTransGen φ.Implies ℓ.negate ℓ) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  by_cases hℓ : σ ℓ.1 = ℓ.2
  · exact (holds_negate σ ℓ).mp (CNF.eval_of_reach hσ h₁ hℓ) hℓ
  · exact hℓ (CNF.eval_of_reach hσ h₂ ((holds_negate σ ℓ).mpr hℓ))

/-- The empty clause refutes a formula. -/
theorem CNF.not_satisfiable_of_nil_mem {φ : CNF V} (h : [] ∈ φ) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  have := (CNF.eval_eq_true_iff σ φ).mp hσ [] h
  simp [Clause.eval] at this

/-- In a clause of width at most two containing `m`, some literal `b` is all that remains besides
`m`. -/
private theorem exists_other {c : Clause V} {m : Literal V} (hc : c.length ≤ 2) (hm : m ∈ c) :
    ∃ b ∈ c, ∀ y ∈ c, y = m ∨ y = b := by
  rcases c with _ | ⟨a, _ | ⟨a', _ | ⟨a'', l⟩⟩⟩
  · exact absurd hm List.not_mem_nil
  · rw [List.mem_singleton] at hm
    subst hm
    exact ⟨m, List.mem_singleton_self m, fun y hy => .inl (List.mem_singleton.mp hy)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨a', by simp, fun y hy => by simpa using hy⟩
    · refine ⟨a, by simp, fun y hy => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact .inr rfl
      · exact .inl rfl
  · simp at hc

open scoped Classical in
/-- **A formula of width at most two is satisfiable** when it has no empty clause and no variable
`x` with a path from `x` to `¬x` and one back [Aspvall, Plass and Tarjan][AspvallPlassTarjan1979].
-/
theorem CNF.satisfiable_of_width_le_two {φ : CNF V} (hw : ∀ c ∈ φ, c.length ≤ 2)
    (hnil : [] ∉ φ)
    (hreach : ∀ v, ¬ (Relation.ReflTransGen φ.Implies (v, true) (v, false) ∧
      Relation.ReflTransGen φ.Implies (v, false) (v, true))) :
    φ.Satisfiable := by
  -- induction on the number of variables
  induction hn : φ.vars.toFinset.card using Nat.strong_induction_on generalizing φ with
  | _ n ih =>
  by_cases hvars : φ.vars = []
  · -- without variables every clause is empty, so there is none
    have hφ : φ = [] := by
      rcases φ with _ | ⟨c, φ⟩
      · rfl
      · have hc : c ≠ [] := fun h => hnil (h ▸ List.mem_cons_self)
        obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil c hc
        have : l.1 ∈ CNF.vars (c :: φ) := CNF.mem_vars.mpr ⟨c, List.mem_cons_self, l.2, hl⟩
        rw [hvars] at this
        exact absurd this (List.not_mem_nil)
    subst hφ
    exact ⟨fun _ => true, rfl⟩
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hvars
  -- a literal of `x` with no path to its negation
  obtain ⟨ℓ, hℓx, hℓ⟩ : ∃ ℓ : Literal V, ℓ.1 = x ∧
      ¬ Relation.ReflTransGen φ.Implies ℓ ℓ.negate := by
    by_cases h : Relation.ReflTransGen φ.Implies (x, true) (x, false)
    · exact ⟨(x, false), rfl, fun h' => hreach x ⟨h, h'⟩⟩
    · exact ⟨(x, true), rfl, h⟩
  -- the literals reachable from `ℓ` are made true
  let R : Literal V → Prop := fun m => Relation.ReflTransGen φ.Implies ℓ m
  have hcons : ∀ m, R m → ¬ R m.negate := by
    intro m hm hm'
    have h' := CNF.reach_negate hm'
    rw [negate_negate] at h'
    exact hℓ (hm.trans h')
  -- the remaining clauses
  let ψ : CNF V := φ.filter fun c => ∀ m ∈ c, ¬ R m ∧ ¬ R m.negate
  have hψφ : ∀ c ∈ ψ, c ∈ φ := fun c hc => (List.mem_filter.mp hc).1
  have hψvars : ψ.vars.toFinset ⊂ φ.vars.toFinset := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨x, List.mem_toFinset.mpr hx, fun hx' => ?_⟩
      obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hx')
      have hall := of_decide_eq_true (List.mem_filter.mp hc).2
      have hm := hall _ hb
      have : (x, b) = ℓ ∨ (x, b) = ℓ.negate := by
        obtain ⟨y, b'⟩ := ℓ
        simp only at hℓx
        subst hℓx
        cases b <;> cases b' <;> simp [Std.Sat.Literal.negate]
      rcases this with h | h
      · exact hm.1 (h ▸ .refl)
      · exact hm.2 (by rw [h, negate_negate])
    · intro y hy
      obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hy)
      exact List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨c, hψφ c hc, b, hb⟩)
  obtain ⟨σ', hσ'⟩ := ih _ (hn ▸ Finset.card_lt_card hψvars)
    (fun c hc => hw c (hψφ c hc)) (fun h => hnil (hψφ _ h))
    (fun v ⟨h₁, h₂⟩ => hreach v
      ⟨Relation.ReflTransGen.mono (fun _ _ (h : ψ.Implies _ _) => h.mono hψφ) _ _ h₁,
        Relation.ReflTransGen.mono (fun _ _ (h : ψ.Implies _ _) => h.mono hψφ) _ _ h₂⟩) rfl
  -- the combined assignment
  let σ : V → Bool := fun v => if R (v, true) then true else if R (v, false) then false else σ' v
  have hR : ∀ m, R m → σ m.1 = m.2 := by
    rintro ⟨v, b⟩ hm
    cases b
    · have : ¬ R (v, true) := fun h => hcons _ hm (by simpa [Std.Sat.Literal.negate] using h)
      simp [σ, this, hm]
    · simp [σ, hm]
  refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr fun c hc => ?_⟩
  by_cases hcψ : ∀ m ∈ c, ¬ R m ∧ ¬ R m.negate
  · -- an untouched clause, satisfied by `σ'`
    have hcψ' : c ∈ ψ := List.mem_filter.mpr ⟨hc, decide_eq_true hcψ⟩
    obtain ⟨m, hm, hmσ⟩ := (Clause.eval_eq_true_iff σ' c).mp
      ((CNF.eval_eq_true_iff σ' ψ).mp hσ' c hcψ')
    refine (Clause.eval_eq_true_iff σ c).mpr ⟨m, hm, ?_⟩
    obtain ⟨v, b⟩ := m
    have h := hcψ _ hm
    have h₁₂ : ¬ R (v, true) ∧ ¬ R (v, false) := by
      cases b
      · exact ⟨h.2, h.1⟩
      · exact h
    simpa [σ, h₁₂.1, h₁₂.2] using hmσ
  · -- a clause with a literal made true or false
    push Not at hcψ
    obtain ⟨m, hm, hmR⟩ := hcψ
    refine (Clause.eval_eq_true_iff σ c).mpr ?_
    by_cases hRm : R m
    · exact ⟨m, hm, hR m hRm⟩
    · obtain ⟨b, hb, hcb⟩ := exists_other (hw c hc) hm
      have harc : φ.Implies m.negate b :=
        ⟨c, hc, by rwa [negate_negate], hb, fun y hy => by rw [negate_negate]; exact hcb y hy⟩
      exact ⟨b, hb, hR b ((hmR hRm).tail harc)⟩

/-- **A formula of width at most two is unsatisfiable exactly when it has the empty clause or a
variable `x` with a path from `x` to `¬x` and one back** [Aspvall, Plass and
Tarjan][AspvallPlassTarjan1979]. -/
theorem CNF.not_satisfiable_iff_of_width_le_two {φ : CNF V} (hw : ∀ c ∈ φ, c.length ≤ 2) :
    ¬ φ.Satisfiable ↔ [] ∈ φ ∨ ∃ v, Relation.ReflTransGen φ.Implies (v, true) (v, false) ∧
      Relation.ReflTransGen φ.Implies (v, false) (v, true) := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h (CNF.satisfiable_of_width_le_two hw h'.1 fun v hv => h'.2 v hv.1 hv.2)
  · rintro (h | ⟨v, h₁, h₂⟩)
    · exact CNF.not_satisfiable_of_nil_mem h
    · exact CNF.not_satisfiable_of_reach (ℓ := (v, true)) h₁ h₂

end Cslib.Logic.PL
