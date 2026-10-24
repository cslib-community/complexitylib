/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Infix

/-!
# Resolution

The *resolvent* of clauses `c₁` and `c₂` on a variable `v` drops the positive literal of `v` from
`c₁` and the negative literal of `v` from `c₂` and joins what remains (`Clause.resolvent`). A clause
is *derivable* from a formula `φ` by resolution if it is a clause of `φ` or the resolvent of two
derivable clauses on a variable occurring positively in the first and negatively in the second
(`CNF.Derives`). Resolution is **sound**: an assignment satisfying both parents satisfies the
resolvent, so a formula from which the empty clause is derivable is unsatisfiable
(`CNF.Derives.not_satisfiable`). It is also **refutation complete**, the ground resolution theorem
of [Robinson1965]: the empty clause is derivable from every unsatisfiable formula
(`CNF.derives_nil_of_not_satisfiable`).

Completeness goes by induction on the number of variables, splitting on a variable as in the
procedure of [DavisPutnam1960]. Fixing a variable `v` of an unsatisfiable formula to either value
(`CNF.restrict`) leaves two unsatisfiable formulas without `v`, from which the empty clause is
derivable. Replaying such a derivation on the original formula derives a clause all of whose
literals are the literal of `v` falsified by the fixed value (`CNF.Derives.exists_of_restrict`).
Either one of the two clauses obtained this way is empty, or they resolve on `v` to the empty
clause.

Clauses are lists, so derivability depends on the order and repetition of literals; there is no
weakening rule.

## Main definitions

* `Cslib.Logic.PL.Clause.resolvent`: the resolvent of two clauses on a variable.
* `Cslib.Logic.PL.CNF.Derives`: derivability by resolution.
* `Cslib.Logic.PL.CNF.restrict`: a formula with one variable fixed.

## Main results

* `Cslib.Logic.PL.CNF.Derives.not_satisfiable`: soundness of resolution refutations.
* `Cslib.Logic.PL.CNF.derives_nil_iff_not_satisfiable`: resolution refutes exactly the
  unsatisfiable formulas.

## References

* [J. A. Robinson, *A machine-oriented logic based on the resolution principle*][Robinson1965]
* [M. Davis, H. Putnam, *A computing procedure for quantification theory*][DavisPutnam1960]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-! ### The resolution rule -/

/-- The resolvent of `c₁` and `c₂` on `v`: the literals of `c₁` other than `v` and those of `c₂`
other than `¬v`. -/
def Clause.resolvent (c₁ c₂ : Clause V) (v : V) : Clause V :=
  c₁.filter (· ≠ (v, true)) ++ c₂.filter (· ≠ (v, false))

/-- A literal belongs to `c₁.resolvent c₂ v` iff it belongs to `c₁` and is not `(v, true)`, or
belongs to `c₂` and is not `(v, false)`. -/
@[simp] theorem Clause.mem_resolvent {c₁ c₂ : Clause V} {v : V} {l : Literal V} :
    l ∈ c₁.resolvent c₂ v ↔ (l ∈ c₁ ∧ l ≠ (v, true)) ∨ (l ∈ c₂ ∧ l ≠ (v, false)) := by
  simp [resolvent]

/-- The resolvent has at most as many literals as its parents together. -/
theorem Clause.length_resolvent_le (c₁ c₂ : Clause V) (v : V) :
    (c₁.resolvent c₂ v).length ≤ c₁.length + c₂.length := by
  rw [resolvent, List.length_append]
  exact Nat.add_le_add (List.length_filter_le _ _) (List.length_filter_le _ _)

/-- **Soundness of one resolution step**: an assignment satisfying both parents satisfies the
resolvent. -/
theorem Clause.eval_resolvent {σ : V → Bool} {c₁ c₂ : Clause V} (v : V)
    (h₁ : c₁.eval σ = true) (h₂ : c₂.eval σ = true) : (c₁.resolvent c₂ v).eval σ = true := by
  rw [Clause.eval_eq_true_iff] at h₁ h₂ ⊢
  obtain ⟨l₁, hl₁, he₁⟩ := h₁
  obtain ⟨l₂, hl₂, he₂⟩ := h₂
  cases hv : σ v
  · refine ⟨l₁, mem_resolvent.2 (Or.inl ⟨hl₁, ?_⟩), he₁⟩
    rintro rfl
    simp [hv] at he₁
  · refine ⟨l₂, mem_resolvent.2 (Or.inr ⟨hl₂, ?_⟩), he₂⟩
    rintro rfl
    simp [hv] at he₂

/-! ### Derivations and soundness -/

/-- The clauses derivable from `φ` by resolution: the clauses of `φ`, and the resolvents of
derivable clauses. -/
inductive CNF.Derives (φ : CNF V) : Clause V → Prop
  /-- A clause of `φ` is derivable. -/
  | mem {c : Clause V} (hc : c ∈ φ) : CNF.Derives φ c
  /-- The resolvent of two derivable clauses on a variable occurring positively in the first and
  negatively in the second is derivable. -/
  | resolvent {c₁ c₂ : Clause V} (v : V) (h₁ : CNF.Derives φ c₁) (h₂ : CNF.Derives φ c₂)
      (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) : CNF.Derives φ (c₁.resolvent c₂ v)

namespace CNF.Derives

variable {φ ψ : CNF V} {c : Clause V}

/-- A derivable clause is true under every assignment satisfying the formula. -/
theorem eval_eq_true (h : φ.Derives c) {σ : V → Bool} (hσ : φ.eval σ = true) :
    c.eval σ = true := by
  induction h with
  | mem hc => exact (CNF.eval_eq_true_iff σ φ).1 hσ _ hc
  | resolvent v _ _ _ _ ih₁ ih₂ => exact Clause.eval_resolvent v ih₁ ih₂

/-- **Soundness of resolution**: a formula from which the empty clause is derivable is
unsatisfiable. -/
theorem not_satisfiable (h : φ.Derives []) : ¬ φ.Satisfiable := fun ⟨_, hσ⟩ => by
  simpa using h.eval_eq_true hσ

/-- Derivations survive adding clauses. -/
theorem mono (h : φ.Derives c) (hφψ : φ ⊆ ψ) : ψ.Derives c := by
  induction h with
  | mem hc => exact mem (hφψ hc)
  | resolvent v _ _ hv₁ hv₂ ih₁ ih₂ => exact resolvent v ih₁ ih₂ hv₁ hv₂

end CNF.Derives

/-! ### Completeness -/

/-- `φ` with the variable `v` fixed to `b`: the clauses satisfied by `v = b` are dropped, and the
literal of `v` falsified by `v = b` is removed from the others. -/
def CNF.restrict (φ : CNF V) (v : V) (b : Bool) : CNF V :=
  (φ.filter fun c => (v, b) ∉ c).map (List.filter (· ≠ (v, !b)))

namespace CNF

variable {φ : CNF V} {v : V} {b : Bool}

/-- A clause belongs to `φ.restrict v b` iff it is obtained from a clause of `φ` not containing
`(v, b)` by removing `(v, !b)`. -/
@[simp] theorem mem_restrict {c : Clause V} :
    c ∈ φ.restrict v b ↔ ∃ d ∈ φ, (v, b) ∉ d ∧ d.filter (· ≠ (v, !b)) = c := by
  simp [restrict, and_assoc]

/-- A restricted formula no longer mentions the fixed variable. -/
theorem fst_ne_of_mem_restrict {c : Clause V} (hc : c ∈ φ.restrict v b) {l : Literal V}
    (hl : l ∈ c) : l.1 ≠ v := by
  obtain ⟨d, -, hvd, rfl⟩ := mem_restrict.1 hc
  obtain ⟨hld, hl⟩ := List.mem_filter.1 hl
  rintro hlv
  obtain ⟨u, a⟩ := l
  subst hlv
  cases a <;> cases b <;> simp_all

/-- The variables of a restricted formula are variables of the formula other than the fixed one. -/
theorem vars_restrict_subset : (φ.restrict v b).vars.toFinset ⊆ φ.vars.toFinset.erase v := by
  intro u hu
  simp only [List.mem_toFinset, vars, List.mem_map, List.mem_flatten] at hu
  obtain ⟨l, ⟨c, hc, hl⟩, rfl⟩ := hu
  refine Finset.mem_erase.2 ⟨fst_ne_of_mem_restrict hc hl, ?_⟩
  obtain ⟨d, hd, -, rfl⟩ := mem_restrict.1 hc
  simp only [List.mem_toFinset, vars, List.mem_map, List.mem_flatten]
  exact ⟨l, ⟨d, hd, (List.mem_filter.1 hl).1⟩, rfl⟩

/-- If `σ` satisfies the restricted formula, then `σ` with `v` set to `b` satisfies the formula. -/
theorem eval_update_of_eval_restrict {σ : V → Bool} (h : (φ.restrict v b).eval σ = true) :
    φ.eval (Function.update σ v b) = true := by
  rw [CNF.eval_eq_true_iff] at h ⊢
  intro d hd
  by_cases hvd : (v, b) ∈ d
  · exact (Clause.eval_eq_true_iff _ _).2 ⟨_, hvd, by simp⟩
  · have hc := h _ (mem_restrict.2 ⟨d, hd, hvd, rfl⟩)
    obtain ⟨l, hl, he⟩ := (Clause.eval_eq_true_iff _ _).1 hc
    refine (Clause.eval_eq_true_iff _ _).2 ⟨l, (List.mem_filter.1 hl).1, ?_⟩
    have hlv := fst_ne_of_mem_restrict (mem_restrict.2 ⟨d, hd, hvd, rfl⟩) hl
    obtain ⟨u, a⟩ := l
    simpa [Function.update_of_ne hlv] using he

/-- Fixing a variable of an unsatisfiable formula leaves an unsatisfiable formula. -/
theorem not_satisfiable_restrict (h : ¬ φ.Satisfiable) : ¬ (φ.restrict v b).Satisfiable :=
  fun ⟨_, hσ⟩ => h ⟨_, eval_update_of_eval_restrict hσ⟩

/-- **Lifting a derivation**: a clause derivable from `φ` with `v` fixed to `b` is contained in a
clause derivable from `φ` that may also contain the literal of `v` falsified by `b`. -/
theorem Derives.exists_of_restrict {c : Clause V} (h : (φ.restrict v b).Derives c) :
    ∃ d, φ.Derives d ∧ (∀ l ∈ d, l ∈ c ∨ l = (v, !b)) ∧ ∀ l ∈ c, l ∈ d := by
  induction h with
  | mem hc =>
    obtain ⟨d, hd, -, rfl⟩ := mem_restrict.1 hc
    refine ⟨d, .mem hd, fun l hl => ?_, fun l hl => (List.mem_filter.1 hl).1⟩
    by_cases hlv : l = (v, !b)
    · exact Or.inr hlv
    · exact Or.inl (List.mem_filter.2 ⟨hl, by simpa using hlv⟩)
  | @resolvent c₁ c₂ u _ _ hu₁ hu₂ ih₁ ih₂ =>
    obtain ⟨d₁, hd₁, h₁, h₁'⟩ := ih₁
    obtain ⟨d₂, hd₂, h₂, h₂'⟩ := ih₂
    refine ⟨d₁.resolvent d₂ u, .resolvent u hd₁ hd₂ (h₁' _ hu₁) (h₂' _ hu₂), fun l hl => ?_,
      fun l hl => ?_⟩
    · rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact (h₁ l hl).imp_left fun hl' => Clause.mem_resolvent.2 (Or.inl ⟨hl', hne⟩)
      · exact (h₂ l hl).imp_left fun hl' => Clause.mem_resolvent.2 (Or.inr ⟨hl', hne⟩)
    · rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact Clause.mem_resolvent.2 (Or.inl ⟨h₁' l hl, hne⟩)
      · exact Clause.mem_resolvent.2 (Or.inr ⟨h₂' l hl, hne⟩)

omit [DecidableEq V] in
/-- A formula without variables is unsatisfiable only if it has the empty clause. -/
private theorem nil_mem_of_vars_eq_nil (hφ : φ.vars = []) (h : ¬ φ.Satisfiable) : [] ∈ φ := by
  by_contra hnil
  refine h ⟨fun _ => false, (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil c fun hc' => hnil (hc' ▸ hc)
  have : l.1 ∈ φ.vars := List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩
  simp [hφ] at this

/-- **Refutation completeness of resolution**: the empty clause is derivable from every
unsatisfiable formula. -/
theorem derives_nil_of_not_satisfiable {φ : CNF V} (h : ¬ φ.Satisfiable) : φ.Derives [] := by
  rcases hφ : φ.vars with _ | ⟨v, _⟩
  · exact .mem (nil_mem_of_vars_eq_nil hφ h)
  have hv : v ∈ φ.vars.toFinset := by simp [hφ]
  -- derivations from both restrictions, by induction on the number of variables
  have hlt (b : Bool) : (φ.restrict v b).vars.toFinset.card < φ.vars.toFinset.card :=
    (Finset.card_le_card vars_restrict_subset).trans_lt (Finset.card_erase_lt_of_mem hv)
  obtain ⟨d₀, hd₀, h₀, -⟩ := (derives_nil_of_not_satisfiable (φ := φ.restrict v false)
    (not_satisfiable_restrict h)).exists_of_restrict
  obtain ⟨d₁, hd₁, h₁, -⟩ := (derives_nil_of_not_satisfiable (φ := φ.restrict v true)
    (not_satisfiable_restrict h)).exists_of_restrict
  -- `d₀` only has `v` and `d₁` only has `¬v`; either one is empty, or they resolve to `[]`
  have h₀' : ∀ l ∈ d₀, l = (v, true) := fun l hl => (h₀ l hl).resolve_left List.not_mem_nil
  have h₁' : ∀ l ∈ d₁, l = (v, false) := fun l hl => (h₁ l hl).resolve_left List.not_mem_nil
  by_cases hv₀ : (v, true) ∈ d₀
  · by_cases hv₁ : (v, false) ∈ d₁
    · convert Derives.resolvent v hd₀ hd₁ hv₀ hv₁ using 1
      refine (List.eq_nil_iff_forall_not_mem.2 fun l hl => ?_).symm
      rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact hne (h₀' l hl)
      · exact hne (h₁' l hl)
    · convert hd₁ using 1
      exact (List.eq_nil_iff_forall_not_mem.2 fun l hl => hv₁ (h₁' l hl ▸ hl)).symm
  · convert hd₀ using 1
    exact (List.eq_nil_iff_forall_not_mem.2 fun l hl => hv₀ (h₀' l hl ▸ hl)).symm
termination_by φ.vars.toFinset.card
decreasing_by
  · exact hlt false
  · exact hlt true

/-- **Resolution refutes exactly the unsatisfiable formulas.** -/
theorem derives_nil_iff_not_satisfiable : φ.Derives [] ↔ ¬ φ.Satisfiable :=
  ⟨Derives.not_satisfiable, derives_nil_of_not_satisfiable⟩

end CNF

end Cslib.Logic.PL
