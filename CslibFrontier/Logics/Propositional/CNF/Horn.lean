/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Polymorphism
public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases

/-!
# Horn formulas and intersection closure

Horn clauses have at most one positive literal occurrence. Models of Horn formulas are closed
under coordinatewise AND. Conversely, every AND-closed Boolean relation on finitely many
coordinates has a Horn definition without auxiliary variables. Empty and nullary relations are
included. The finite-extension proof is original; the characterization is [Bodirsky2026],
Lemma 6.31, pp. 75–76 (September 14, 2026 version), with finite coordinate types replacing
numbered variables and `false`/`true` replacing 0/1. See [Chen2006CSP], Section 4, for the
corresponding Boolean CSP tractability cases.

Flipping every literal polarity gives the dual Horn characterization for coordinatewise OR.
These are semantic normal-form theorems; no efficient construction of the normal form is claimed.

## Main results

* `Cslib.Logic.PL.isPolymorphism_and_iff_exists_hornCNF`: AND preservation iff Horn definability.
* `Cslib.Logic.PL.isPolymorphism_or_iff_exists_dualHornCNF`: the dual OR characterization.
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-- At most one positive literal occurrence, counting repetitions. -/
@[expose] def Clause.IsHorn (c : Clause V) : Prop := (c.filter Prod.snd).length ≤ 1

/-- Every clause has at most one positive literal occurrence. -/
@[expose] def CNF.IsHorn (φ : CNF V) : Prop := ∀ c ∈ φ, c.IsHorn

/-- Binary AND preservation is closure under pointwise conjunction. -/
theorem isPolymorphism_and_iff (R : Set (V → Bool)) :
    IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1) R ↔
      ∀ x ∈ R, ∀ y ∈ R, (fun i => x i && y i) ∈ R := by
  constructor
  · intro h x hx y hy
    exact h (fun j => if j = 0 then x else y) (by intro j; fin_cases j <;> assumption)
  · intro h a ha
    exact h (a 0) (ha 0) (a 1) (ha 1)

/-- A Horn clause cannot have two different positive literals. Repetition still counts in
`IsHorn`, so this necessary condition is not a characterization. -/
theorem Clause.IsHorn.positive_unique {c : Clause V} (hc : c.IsHorn)
    {p q : Literal V} (hp : p ∈ c) (hq : q ∈ c) (hp' : p.2 = true) (hq' : q.2 = true) :
    p = q := by
  have hp'' : p ∈ c.filter Prod.snd := List.mem_filter.mpr ⟨hp, hp'⟩
  have hq'' : q ∈ c.filter Prod.snd := List.mem_filter.mpr ⟨hq, hq'⟩
  cases hcs : c.filter Prod.snd with
  | nil => simp [hcs] at hp''
  | cons r rs =>
    cases rs with
    | nil => simp only [hcs, List.mem_singleton] at hp'' hq''; exact hp''.trans hq''.symm
    | cons t ts => simp [Clause.IsHorn, hcs] at hc

/-- A Horn clause is preserved by coordinatewise conjunction, including negative-only and empty
clauses, repeated negative literals and tautologies. -/
theorem Clause.eval_and_of_isHorn {c : Clause V} (hc : c.IsHorn)
    {x y : V → Bool} (hx : c.eval x = true) (hy : c.eval y = true) :
    c.eval (fun i => x i && y i) = true := by
  obtain ⟨p, hp, hpx⟩ := (Clause.eval_eq_true_iff _ _).mp hx
  obtain ⟨q, hq, hqy⟩ := (Clause.eval_eq_true_iff _ _).mp hy
  by_cases hp' : p.2 = true
  · by_cases hq' : q.2 = true
    · have heq := hc.positive_unique hp hq hp' hq'
      subst q
      exact (Clause.eval_eq_true_iff _ _).mpr ⟨p, hp, by simp [hpx, hqy, hp']⟩
    · exact (Clause.eval_eq_true_iff _ _).mpr ⟨q, hq, by
        cases hqv : q.2 <;> simp_all⟩
  · exact (Clause.eval_eq_true_iff _ _).mpr ⟨p, hp, by
      cases hpv : p.2 <;> simp_all⟩

/-- Models of a Horn CNF are AND-preserved. -/
theorem CNF.isPolymorphism_and {φ : CNF V} (hφ : φ.IsHorn) :
    IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1) {a | φ.eval a = true} := by
  rw [isPolymorphism_and_iff]
  intro x hx y hy
  exact (CNF.eval_eq_true_iff _ _).mpr fun c hc =>
    c.eval_and_of_isHorn (hφ c hc) ((CNF.eval_eq_true_iff _ _).mp hx c hc)
      ((CNF.eval_eq_true_iff _ _).mp hy c hc)

/-- Finite intersections of extensions of a tuple recover that tuple when every false
coordinate can be made false by such an extension. Nonemptiness handles nullary relations. -/
theorem mem_of_extensions_of_and [Finite V] {R : Set (V → Bool)}
    (hR : IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1) R) (a : V → Bool)
    (hne : ∃ b ∈ R, ∀ i, a i = true → b i = true)
    (hext : ∀ i, a i = false → ∃ b ∈ R, b i = false ∧
      ∀ j, a j = true → b j = true) : a ∈ R := by
  classical
  let _ := Fintype.ofFinite V
  have hclosed := (isPolymorphism_and_iff R).mp hR
  have extend (s : Finset V) : ∃ b ∈ R, (∀ i, a i = true → b i = true) ∧
      ∀ i ∈ s, b i = a i := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨b, hb, hba⟩ := hne
      exact ⟨b, hb, hba, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨b, hb, hba, hbs⟩ := ih
      cases hai : a i with
      | true =>
        refine ⟨b, hb, hba, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (hba j hai).trans hai.symm
        · exact hbs j hj
      | false =>
        obtain ⟨c, hc, hci, hca⟩ := hext i hai
        refine ⟨fun j => b j && c j, hclosed b hb c hc, ?_, ?_⟩
        · intro j hj
          simp [hba j hj, hca j hj]
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · simp [hci, hai]
          · change (b j && c j) = a j
            rw [hbs j hj]
            cases haj : a j with
            | false => simp
            | true => simp [hca j haj]
  obtain ⟨b, hb, _, hba⟩ := extend Finset.univ
  have : b = a := funext fun i => hba i (Finset.mem_univ i)
  rwa [this] at hb

/-- A tuple outside a finite AND-closed relation is separated by a Horn clause over the same
variables. -/
theorem exists_separating_clause_of_and [Finite V] {R : Set (V → Bool)}
    (hR : IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1) R)
    {a : V → Bool} (ha : a ∉ R) :
    ∃ c : Clause V, c.IsHorn ∧ (∀ b ∈ R, c.eval b = true) ∧ c.eval a = false := by
  classical
  let _ := Fintype.ofFinite V
  let ns : Clause V := ((Finset.univ.toList.filter fun i => a i).map fun i => (i, false))
  have hns (b : V → Bool) : ns.eval b = true ↔ ∃ i, a i = true ∧ b i = false := by
    simp [ns, Clause.eval_eq_true_iff]
  have hnsHorn : ns.IsHorn := by simp [Clause.IsHorn, ns, List.filter_map]
  have hnsa : ns.eval a = false := by
    cases h : ns.eval a
    · rfl
    · obtain ⟨i, hi, hi'⟩ := (hns a).mp h
      simp_all
  by_cases hne : ∃ b ∈ R, ∀ i, a i = true → b i = true
  · have hn : ¬ ∀ i, a i = false → ∃ b ∈ R, b i = false ∧
        ∀ j, a j = true → b j = true := fun h => ha (mem_of_extensions_of_and hR a hne h)
    push Not at hn
    obtain ⟨i, hai, hi⟩ := hn
    refine ⟨(i, true) :: ns, ?_, ?_, ?_⟩
    · simp [Clause.IsHorn, ns, List.filter_map]
    · intro b hb
      by_cases hba : ∀ j, a j = true → b j = true
      · have hbi : b i = true := by
          cases h : b i
          · obtain ⟨j, haj, hbj⟩ := hi b hb h
            exact (hbj (hba j haj)).elim
          · rfl
        simp [hbi]
      · have : ∃ j, a j = true ∧ b j = false := by
          push Not at hba
          obtain ⟨j, haj, hbj⟩ := hba
          exact ⟨j, haj, by simpa using hbj⟩
        simp [((hns b).mpr this)]
    · simp [hai, hnsa]
  · refine ⟨ns, hnsHorn, ?_, hnsa⟩
    intro b hb
    apply (hns b).mpr
    have hn : ¬ ∀ i, a i = true → b i = true := fun h => hne ⟨b, hb, h⟩
    push Not at hn
    obtain ⟨i, hai, hbi⟩ := hn
    exact ⟨i, hai, by simpa using hbi⟩

/-- Finite Boolean AND-preserved relations are exactly Horn CNF relations, with no auxiliaries.
Empty relations and empty coordinate types are included. -/
theorem isPolymorphism_and_iff_exists_hornCNF [Finite V] (R : Set (V → Bool)) :
    IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1) R ↔
      ∃ φ : CNF V, φ.IsHorn ∧ ∀ a, a ∈ R ↔ φ.eval a = true := by
  classical
  let _ := Fintype.ofFinite V
  constructor
  · intro hR
    let tuples : List (V → Bool) := Finset.univ.toList
    let bad := tuples.filter fun a => a ∉ R
    have sep : ∀ a ∈ bad, ∃ c : Clause V, c.IsHorn ∧
        (∀ b ∈ R, c.eval b = true) ∧ c.eval a = false := by
      intro a ha
      exact exists_separating_clause_of_and hR (of_decide_eq_true (List.mem_filter.mp ha).2)
    choose cs hcs using fun a : {a // a ∈ bad} => sep a.1 a.2
    let φ : CNF V := bad.attach.map cs
    refine ⟨φ, ?_, fun a => ⟨?_, ?_⟩⟩
    · intro c hc
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
      exact (hcs b).1
    · intro ha
      exact (CNF.eval_eq_true_iff _ _).mpr fun c hc => by
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
        exact (hcs b).2.1 a ha
    · intro ha
      by_contra hn
      have hbad : a ∈ bad := by simp [bad, tuples, hn]
      have hm : cs ⟨a, hbad⟩ ∈ φ := List.mem_map.mpr ⟨⟨a, hbad⟩, by simp, rfl⟩
      have ht := (CNF.eval_eq_true_iff _ _).mp ha _ hm
      rw [(hcs ⟨a, hbad⟩).2.2] at ht
      contradiction
  · rintro ⟨φ, hφ, heq⟩
    have : R = {a | φ.eval a = true} := Set.ext heq
    rw [this]
    exact CNF.isPolymorphism_and hφ

/-- Complement the polarity of every literal, without changing variables or occurrences. -/
@[expose] def Clause.flip (c : Clause V) : Clause V := c.map Std.Sat.Literal.negate

/-- Complement every literal polarity in a formula. -/
@[expose] def CNF.flip (φ : CNF V) : CNF V := φ.map Clause.flip

/-- A dual Horn clause has at most one negative literal occurrence. -/
@[expose] def Clause.IsDualHorn (c : Clause V) : Prop := c.flip.IsHorn

/-- A formula is dual Horn when all its clauses are dual Horn. -/
@[expose] def CNF.IsDualHorn (φ : CNF V) : Prop := φ.flip.IsHorn

/-- The polarity-flipping definition counts exactly the negative literal occurrences. -/
theorem Clause.isDualHorn_iff (c : Clause V) :
    c.IsDualHorn ↔ (c.filter fun l => !l.2).length ≤ 1 := by
  simp only [Clause.IsDualHorn, Clause.IsHorn, Clause.flip, List.filter_map, List.length_map]
  rfl

/-- Dual Horn syntax can be checked one clause at a time. -/
theorem CNF.isDualHorn_iff (φ : CNF V) : φ.IsDualHorn ↔ ∀ c ∈ φ, c.IsDualHorn := by
  simp [CNF.IsDualHorn, CNF.IsHorn, CNF.flip, Clause.IsDualHorn]

/-- Complementing polarities is an involution on clauses. -/
@[simp] theorem Clause.flip_flip (c : Clause V) : c.flip.flip = c := by
  simp [Clause.flip, List.map_map, Function.comp_def, Std.Sat.Literal.negate]

/-- Complementing polarities is an involution on formulas. -/
@[simp] theorem CNF.flip_flip (φ : CNF V) : φ.flip.flip = φ := by
  simp [CNF.flip, List.map_map, Function.comp_def]

/-- Flipping polarities evaluates a clause under the complemented assignment. -/
@[simp] theorem Clause.eval_flip (c : Clause V) (a : V → Bool) :
    c.flip.eval a = c.eval (fun i => !a i) := by
  simp only [Clause.flip, Clause.eval, List.any_map]
  congr 1 with l : 1
  obtain ⟨v, b⟩ := l
  cases hv : a v <;> cases b <;> simp [Std.Sat.Literal.negate, Literal.eval, hv]

/-- Flipping polarities evaluates a formula under the complemented assignment. -/
@[simp] theorem CNF.eval_flip (φ : CNF V) (a : V → Bool) :
    φ.flip.eval a = φ.eval (fun i => !a i) := by
  simp [CNF.flip, CNF.eval, List.all_map, Function.comp_def]

/-- Complementing all variables preserves satisfiability. -/
@[simp] theorem CNF.satisfiable_flip (φ : CNF V) : φ.flip.Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun i => !a i, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun i => !a i, by simpa using ha⟩

/-- Coordinatewise OR preservation becomes AND preservation under complementation. -/
theorem isPolymorphism_or_iff_and_complement (R : Set (V → Bool)) :
    IsPolymorphism (fun a : Fin 2 → Bool => a 0 || a 1) R ↔
      IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1)
        {a | (fun i => !a i) ∈ R} := by
  rw [isPolymorphism_and_iff]
  constructor
  · intro h x hx y hy
    have ht : ∀ j : Fin 2, (if j = 0 then (fun i => !x i) else (fun i => !y i)) ∈ R := by
      intro j
      fin_cases j <;> assumption
    simpa [Bool.not_and] using h _ ht
  · intro h a ha
    have hx : (fun i => !(a 0 i)) ∈ {a | (fun i => !a i) ∈ R} := by simpa using ha 0
    have hy : (fun i => !(a 1 i)) ∈ {a | (fun i => !a i) ∈ R} := by simpa using ha 1
    simpa only [Set.mem_ofPred_eq, Bool.not_and, Bool.not_not] using h _ hx _ hy

/-- Models of a dual Horn CNF are OR-preserved, with no finiteness requirement on variables. -/
theorem CNF.isPolymorphism_or {φ : CNF V} (hφ : φ.IsDualHorn) :
    IsPolymorphism (fun a : Fin 2 → Bool => a 0 || a 1) {a | φ.eval a = true} := by
  rw [isPolymorphism_or_iff_and_complement]
  simpa only [CNF.eval_flip, Set.mem_ofPred_eq] using CNF.isPolymorphism_and hφ

/-- Finite OR-preserved Boolean relations are exactly dual Horn CNF relations, without
auxiliary variables. -/
theorem isPolymorphism_or_iff_exists_dualHornCNF [Finite V] (R : Set (V → Bool)) :
    IsPolymorphism (fun a : Fin 2 → Bool => a 0 || a 1) R ↔
      ∃ φ : CNF V, φ.IsDualHorn ∧ ∀ a, a ∈ R ↔ φ.eval a = true := by
  rw [isPolymorphism_or_iff_and_complement, isPolymorphism_and_iff_exists_hornCNF]
  constructor
  · rintro ⟨φ, hφ, heq⟩
    refine ⟨φ.flip, by simpa [CNF.IsDualHorn] using hφ, ?_⟩
    intro a
    simpa using heq (fun i => !a i)
  · rintro ⟨φ, hφ, heq⟩
    exact ⟨φ.flip, hφ, fun a => by simpa using heq (fun i => !a i)⟩

end Cslib.Logic.PL
